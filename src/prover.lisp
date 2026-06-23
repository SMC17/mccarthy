;;;; src/prover.lisp — the AGENTIC layer (untrusted).
;;;;
;;;; * an s-expression surface parser (homoiconic: goals ARE s-exprs)
;;;; * a goal-directed tactic engine + tacticals
;;;; * `solve`: an automatic prover combining backward decomposition with
;;;;   forward saturation, SYNTHESIZING specialized inference steps (universal
;;;;   instantiation at guessed witnesses, modus ponens, conjunction splitting)
;;;;   as first-class data during search.
;;;; * a learned-fact registry: proved theorems can be fed back into the search
;;;;   as reusable lemmas — the reflective self-extension the Lisp substrate
;;;;   makes natural.  Every proof it finds is still certified by the kernel.

(in-package :mccarthy)

(export '(parse-type parse-term prove-sexp solve auto-prove
          learn forget *facts* facts is-true
          gtac-conj gtac-disch gtac-gen gtac-assumption prove-with))

;;; ---- surface syntax: s-expr -> kernel term ---------------------------------

(defun parse-type (s)
  (cond ((symbolp s)
         (cond ((string-equal (string s) "bool") (bool-ty))
               (t (make-htvar (string-upcase (string s))))))
        ((consp s)
         (case (intern (string-upcase (string (car s))) :keyword)
           ((:fun :->) (mk-fun (parse-type (second s)) (parse-type (third s))))
           (t (mk-type (string-downcase (string (car s))) (mapcar #'parse-type (cdr s))))))
        (t (error "bad type ~s" s))))

(defun %key (s) (and (symbolp s) (intern (string-upcase (string s)) :keyword)))

(defun parse-term (s env)
  "ENV is an alist of (name-string . htype) for the non-logical signature."
  (cond
    ((symbolp s)
     (let ((p (assoc (string s) env :test #'string-equal)))
       (cond (p (mk-var (string-upcase (string s)) (cdr p)))
             ((string-equal (string s) "T") (mk-t))
             ((string-equal (string s) "F") (mk-false))
             (t (error "unbound symbol ~a — declare it in the signature" s)))))
    ((consp s)
     (case (%key (car s))
       (:= (mk-eq (parse-term (second s) env) (parse-term (third s) env)))
       ((:and :/\\) (mk-conj (parse-term (second s) env) (parse-term (third s) env)))
       ((:==> :imp :=>) (mk-imp (parse-term (second s) env) (parse-term (third s) env)))
       ((:\\/ :or) (mk-disj (parse-term (second s) env) (parse-term (third s) env)))
       ((:~ :not) (mk-neg (parse-term (second s) env)))
       ((:! :forall)
        (destructuring-bind ((vn vty) body) (cdr s)
          (let* ((ty (parse-type vty)) (v (mk-var (string-upcase (string vn)) ty)))
            (mk-forall v (parse-term body (acons (string vn) ty env))))))
       ((:lam :lambda)
        (destructuring-bind ((vn vty) body) (cdr s)
          (let* ((ty (parse-type vty)) (v (mk-var (string-upcase (string vn)) ty)))
            (mk-abs v (parse-term body (acons (string vn) ty env))))))
       (t (list-mk-comb (parse-term (car s) env) (mapcar (lambda (x) (parse-term x env)) (cdr s))))))
    (t (error "bad term ~s" s))))

(defun is-true (tm) (and (hconst-p tm) (string= (hconst-name tm) "T")))

;;; ---- learned-fact registry (reflective self-extension) ---------------------

(defvar *facts* '() "Global certified lemmas folded into every search.")
(defun learn (th)
  "Add a certified theorem to the reusable fact base."
  (unless (thm-p th) (error "learn: not a theorem"))
  (pushnew th *facts* :test (lambda (a b) (aconv (concl a) (concl b))))
  th)
(defun forget () (setf *facts* '()))
(defun facts () (mapcar #'concl *facts*))

;;; ---- witness synthesis -----------------------------------------------------

(defun subterms (tm)
  (cons tm (cond ((hcomb-p tm) (append (subterms (hcomb-rator tm)) (subterms (hcomb-rand tm))))
                 ((habs-p tm) (subterms (habs-body tm)))
                 (t nil))))
(defun terms-of-type (tms ty)
  (remove-duplicates
   (remove-if (lambda (s) (or (habs-p s) (not (type= (type-of s) ty)))) (mapcan #'subterms (copy-list tms)))
   :test #'aconv))

;;; ---- forward saturation: grow the assumption set with derived facts --------

(defun fact-known (th pool) (member (concl th) pool :key #'concl :test #'aconv))

(defun forward-close (asms witnesses &optional (rounds 3))
  "Close ASMS under conjunction-splitting, universal instantiation at WITNESSES,
   and modus ponens.  Every added element is a real kernel theorem."
  (let ((pool (copy-list asms)))
    (dotimes (i rounds)
      (let ((new '()))
        (dolist (a pool)
          (let ((c (concl a)))
            (cond
              ((is-conj c)
               (let ((l (conjunct1 a)) (r (conjunct2 a)))
                 (unless (fact-known l pool) (push l new))
                 (unless (fact-known r pool) (push r new))))
              ((is-forall c)
               (let ((ty (hvar-ty (nth-value 0 (dest-forall c)))))
                 (dolist (w (terms-of-type witnesses ty))
                   (let ((sp (ignore-errors (spec w a))))
                     (when (and sp (not (fact-known sp pool)) (not (fact-known sp new)))
                       (push sp new))))))
              ((is-imp c)
               (mvb (p q) (dest-imp c) (declare (ignore q))
                 (let ((pp (find p pool :key #'concl :test #'aconv)))
                   (when pp (let ((res (ignore-errors (mp a pp))))
                              (when (and res (not (fact-known res pool))) (push res new)))))))
              ((is-neg c)                       ; ~p  behaves as  p ==> F
               (let ((ne (ignore-errors (not-elim a))))
                 (when (and ne (not (fact-known ne pool))) (push ne new)))))))
        (setf new (remove-duplicates new :test (lambda (x y) (aconv (concl x) (concl y)))))
        (when (null new) (return))
        (setf pool (nconc pool new))))
    pool))

;;; ---- the automatic prover --------------------------------------------------

(defun solve (asms w depth)
  "Return a kernel theorem proving W from assumptions ASMS (list of thms), or NIL.
   ASMS implicitly includes the global *facts*."
  (when (minusp depth) (return-from solve nil))
  (let* ((all (append *facts* asms))
         (witnesses (cons w (mapcar #'concl all)))
         (pool (forward-close all witnesses 3)))
    ;; closed goals: assumption hit, truth, reflexivity
    (dolist (a pool) (when (aconv (concl a) w) (return-from solve a)))
    (when (is-true w) (return-from solve (truth)))
    (when (and (is-eq w) (mvb (l r) (dest-eq w) (aconv l r)))
      (return-from solve (refl (nth-value 0 (dest-eq w)))))
    ;; ex falso: a contradiction in the (saturated) assumptions proves anything
    (let ((fth (find-if (lambda (a) (is-false (concl a))) pool)))
      (when fth (return-from solve (contr w fth))))
    ;; backward structural decomposition
    (or
     (cond
       ((is-conj w)
        (mvb (a b) (dest-conj w)
          (let ((pa (solve asms a (1- depth))))
            (when pa (let ((pb (solve asms b (1- depth)))) (when pb (conj pa pb)))))))
       ((is-imp w)
        (mvb (a b) (dest-imp w)
          (let ((pb (solve (cons (assume a) asms) b (1- depth)))) (when pb (disch a pb)))))
       ((is-forall w)
        (mvb (x bod) (dest-forall w)
          (let* ((x2 (variant (free-vars-list (mapcar #'concl all)) x))
                 (bod2 (vsubst (list (cons x x2)) bod))
                 (pb (solve asms bod2 (1- depth))))
            (when pb (gen x2 pb)))))
       ((is-disj w)                         ; prove either disjunct
        (mvb (a b) (dest-disj w)
          (let ((pl (solve asms a (1- depth))))
            (if pl (disj1 pl b)
                (let ((pr (solve asms b (1- depth)))) (when pr (disj2 a pr)))))))
       ((is-neg w)                          ; ~p  <=>  p ==> F
        (let* ((p (dest-neg w))
               (pf (solve (cons (assume p) asms) (mk-false) (1- depth))))
          (when pf (not-intro (disch p pf)))))
       (t nil))
     ;; case-split on a disjunctive assumption
     (solve-by-disjunction asms pool w depth)
     ;; equational search step: rewrite the goal with one oriented equation
     ;; drawn from the (saturated) assumptions, then recurse.  Each step is a
     ;; certified  |- w = w'  so the recovered proof stays kernel-checked.
     (solve-by-rewriting asms pool w depth))))

(defun solve-by-disjunction (asms pool w depth)
  "If an assumption is  l \\/ r, prove W under each disjunct and combine."
  (dolist (a pool nil)
    (when (is-disj (concl a))
      (mvb (l r) (dest-disj (concl a))
        (let ((pl (solve (cons (assume l) asms) w (1- depth))))
          (when pl
            (let ((pr (solve (cons (assume r) asms) w (1- depth))))
              (when pr (return (disj-cases a pl pr))))))))))

(defun oriented-eq-rules (pool)
  "Equational theorems in POOL, both orientations, usable as rewrite rules."
  (loop for a in pool when (is-eq (concl a))
        append (list a (sym a))))

(defun solve-by-rewriting (asms pool w depth)
  (dolist (e (oriented-eq-rules pool) nil)
    (let* ((conv (bounded-depth-conv (rewr-conv e)))
           (eqth (ignore-errors (funcall conv w)))
           (w2 (and eqth (nth-value 1 (dest-eq (concl eqth))))))
      (when (and w2 (not (aconv w2 w)))
        (let ((pf (solve asms w2 (1- depth))))
          (when pf (return (eq-mp (sym eqth) pf))))))))

(defun auto-prove (term &key (depth 12))
  "Top-level: attempt to certify TERM. Returns a kernel thm or NIL."
  (solve '() term depth))

;;; ---- entry point: parse + prove --------------------------------------------

(defun build-env (sig)
  (mapcar (lambda (d) (cons (string (first d)) (parse-type (second d)))) sig))

(defun prove-sexp (sig goal-sexp &key (depth 12))
  "Parse GOAL-SEXP under signature SIG and attempt an automatic certified proof.
   Returns (values thm-or-nil parsed-goal-term)."
  (let* ((env (build-env sig))
         (goal (parse-term goal-sexp env))
         (th (auto-prove goal :depth depth)))
    (when (and th (not (aconv (concl th) goal)))
      (error "internal: produced theorem does not match goal"))
    (values th goal)))
