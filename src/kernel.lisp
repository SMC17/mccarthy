;;;; McCarthy — the Aristotle of Lisp
;;;; src/kernel.lisp — the TRUSTED KERNEL.
;;;;
;;;; This is the only soundness-critical file. It implements a higher-order
;;;; logic (simply-typed lambda calculus + equality) in the LCF tradition:
;;;; the type THM is opaque, and the ONLY way to obtain a THM is through the
;;;; ten primitive inference rules below (plus definitional extension).
;;;; Everything in every other file is untrusted: it can only build proofs by
;;;; calling these rules, so soundness reduces to the correctness of THIS file.
;;;;
;;;; De Bruijn criterion: keep this kernel small, auditable, and closed.
;;;; Design follows John Harrison's HOL Light `fusion.ml`, ported to s-exprs.

(defpackage :mccarthy.kernel
  (:use :cl)
  (:shadow #:type-of)
  (:export
   ;; type representation
   #:htype #:htvar #:htapp #:make-htvar #:make-htapp
   #:htvar-p #:htapp-p #:htvar-name #:htapp-op #:htapp-args
   #:type= #:type-subst #:type-vars #:bool-ty #:fun-ty #:a-ty #:mk-fun
   #:declare-type #:get-type-arity #:mk-type
   ;; term representation
   #:term #:hvar #:hconst #:hcomb #:habs
   #:hvar-p #:hconst-p #:hcomb-p #:habs-p
   #:hvar-name #:hvar-ty #:hconst-name #:hconst-ty
   #:hcomb-rator #:hcomb-rand #:habs-bv #:habs-body
   #:type-of #:term= #:aconv #:frees #:vfree-in #:variant #:free-vars-list
   #:mk-var #:mk-const #:mk-comb #:mk-abs #:list-mk-comb #:list-mk-abs
   #:mk-eq #:dest-eq #:is-eq #:dest-comb #:dest-abs #:rator #:rand
   #:vsubst #:inst-term #:declare-const #:get-const-type #:constants
   ;; the opaque theorem type + its observers
   #:thm #:thm-p #:hyp #:concl
   ;; the ten primitive rules
   #:prim-refl #:prim-trans #:prim-mk-comb #:prim-abs #:prim-beta
   #:prim-assume #:prim-eq-mp #:prim-deduct #:prim-inst #:prim-inst-type
   ;; definitional extension
   #:new-axiom #:new-basic-definition #:axioms #:definitions
   ;; conditions
   #:kernel-error))

(in-package :mccarthy.kernel)

(define-condition kernel-error (error)
  ((msg :initarg :msg :reader kernel-error-msg))
  (:report (lambda (c s) (format s "kernel-error: ~a" (kernel-error-msg c)))))
(defun kfail (fmt &rest args) (error 'kernel-error :msg (apply #'format nil fmt args)))

;;; ----------------------------------------------------------------------------
;;; TYPES.  hol_type = Htvar name | Htapp(op, args)
;;; ----------------------------------------------------------------------------

(defstruct (htvar (:constructor make-htvar (name))) name)
(defstruct (htapp (:constructor make-htapp (op args))) op args)

(defun type= (a b)
  (cond ((and (htvar-p a) (htvar-p b)) (string= (htvar-name a) (htvar-name b)))
        ((and (htapp-p a) (htapp-p b))
         (and (string= (htapp-op a) (htapp-op b))
              (= (length (htapp-args a)) (length (htapp-args b)))
              (every #'type= (htapp-args a) (htapp-args b))))
        (t nil)))

;; registry of type constructors -> arity
(defvar *type-arities* (make-hash-table :test 'equal))
(defun declare-type (name arity)
  (let ((cur (gethash name *type-arities*)))
    (when (and cur (/= cur arity)) (kfail "type ~a already declared with arity ~a" name cur))
    (setf (gethash name *type-arities*) arity)))
(defun get-type-arity (name)
  (or (gethash name *type-arities*) (kfail "unknown type constructor ~a" name)))

(defun mk-type (op args)
  (let ((ar (get-type-arity op)))
    (unless (= ar (length args)) (kfail "type ~a expects ~a args, got ~a" op ar (length args)))
    (make-htapp op args)))

(declare-type "bool" 0)
(declare-type "fun" 2)
(declare-type "ind" 0)

(defun bool-ty () (make-htapp "bool" '()))
(defun a-ty () (make-htvar "A"))
(defun mk-fun (dom cod) (make-htapp "fun" (list dom cod)))
(defun fun-ty (dom cod) (mk-fun dom cod))

(defun type-subst (theta ty)         ; theta: alist (tyvar-name-string . htype)
  (cond ((htvar-p ty)
         (let ((p (assoc (htvar-name ty) theta :test #'string=)))
           (if p (cdr p) ty)))
        ((htapp-p ty)
         (make-htapp (htapp-op ty) (mapcar (lambda (x) (type-subst theta x)) (htapp-args ty))))))

(defun type-vars (ty &optional acc)
  (cond ((htvar-p ty) (if (member (htvar-name ty) acc :test #'string=) acc
                          (cons (htvar-name ty) acc)))
        ((htapp-p ty) (dolist (a (htapp-args ty) acc) (setf acc (type-vars a acc))))))

;;; ----------------------------------------------------------------------------
;;; TERMS.  term = Hvar | Hconst | Hcomb | Habs
;;; ----------------------------------------------------------------------------

(defstruct (hvar   (:constructor make-hvar (name ty)))   name ty)
(defstruct (hconst (:constructor make-hconst (name ty))) name ty)
(defstruct (hcomb  (:constructor make-hcomb (rator rand))) rator rand)
(defstruct (habs   (:constructor make-habs (bv body)))   bv body)

;; registry of constants -> generic type
(defvar *constants* (make-hash-table :test 'equal))
(defun declare-const (name generic-ty)
  (when (gethash name *constants*) (kfail "constant ~a already declared" name))
  (setf (gethash name *constants*) generic-ty))
(defun get-const-type (name)
  (or (gethash name *constants*) (kfail "unknown constant ~a" name)))
(defun constants () (loop for k being the hash-keys of *constants* collect k))

;; the single primitive constant: equality, generic type A->A->bool
(declare-const "=" (mk-fun (a-ty) (mk-fun (a-ty) (bool-ty))))

;; exact (non-alpha) structural equality
(defun term= (a b)
  (cond ((and (hvar-p a) (hvar-p b))
         (and (string= (hvar-name a) (hvar-name b)) (type= (hvar-ty a) (hvar-ty b))))
        ((and (hconst-p a) (hconst-p b))
         (and (string= (hconst-name a) (hconst-name b)) (type= (hconst-ty a) (hconst-ty b))))
        ((and (hcomb-p a) (hcomb-p b))
         (and (term= (hcomb-rator a) (hcomb-rator b)) (term= (hcomb-rand a) (hcomb-rand b))))
        ((and (habs-p a) (habs-p b))
         (and (term= (habs-bv a) (habs-bv b)) (term= (habs-body a) (habs-body b))))
        (t nil)))

(defun type-of (tm)
  (cond ((hvar-p tm) (hvar-ty tm))
        ((hconst-p tm) (hconst-ty tm))
        ((hcomb-p tm) (second (htapp-args (type-of (hcomb-rator tm)))))
        ((habs-p tm) (mk-fun (hvar-ty (habs-bv tm)) (type-of (habs-body tm))))))

;;; alpha-equivalence.  env pairs bound vars of t1 with bound vars of t2.
(defun bv-match (v1 v2 env)
  (dolist (pr env :free)
    (let ((m1 (term= v1 (car pr))) (m2 (term= v2 (cdr pr))))
      (when (or m1 m2) (return (if (and m1 m2) :match :nomatch))))))

(defun orda (t1 t2 env)
  (cond ((and (hvar-p t1) (hvar-p t2))
         (case (bv-match t1 t2 env) (:match t) (:nomatch nil) (:free (term= t1 t2))))
        ((and (hconst-p t1) (hconst-p t2)) (term= t1 t2))
        ((and (hcomb-p t1) (hcomb-p t2))
         (and (orda (hcomb-rator t1) (hcomb-rator t2) env)
              (orda (hcomb-rand t1) (hcomb-rand t2) env)))
        ((and (habs-p t1) (habs-p t2))
         (and (type= (hvar-ty (habs-bv t1)) (hvar-ty (habs-bv t2)))
              (orda (habs-body t1) (habs-body t2)
                    (cons (cons (habs-bv t1) (habs-bv t2)) env))))
        (t nil)))
(defun aconv (t1 t2) (orda t1 t2 '()))

(defun vfree-in (v tm)
  (cond ((habs-p tm) (and (not (term= v (habs-bv tm))) (vfree-in v (habs-body tm))))
        ((hcomb-p tm) (or (vfree-in v (hcomb-rator tm)) (vfree-in v (hcomb-rand tm))))
        ((hconst-p tm) nil)
        ((hvar-p tm) (term= v tm))))

(defun union-term (l1 l2) ; exact union (by term=)
  (dolist (x l1 l2) (unless (member x l2 :test #'term=) (push x l2))))
(defun frees (tm)
  (cond ((hvar-p tm) (list tm))
        ((hconst-p tm) '())
        ((hcomb-p tm) (union-term (frees (hcomb-rator tm)) (frees (hcomb-rand tm))))
        ((habs-p tm) (remove (habs-bv tm) (frees (habs-body tm)) :test #'term=))))
(defun free-vars-list (tms) (reduce #'union-term (mapcar #'frees tms) :initial-value '()))

(defun variant (avoid v)               ; fresh variant of var V avoiding free occurrences in AVOID
  (if (some (lambda (a) (vfree-in v a)) avoid)
      (variant avoid (make-hvar (concatenate 'string (hvar-name v) "'") (hvar-ty v)))
      v))

;;; capture-avoiding term substitution.  theta: alist (var . replacement-term).
(defun vsubst-typecheck (theta)
  (dolist (p theta)
    (unless (hvar-p (car p)) (kfail "vsubst: lhs not a var"))
    (unless (type= (type-of (car p)) (type-of (cdr p))) (kfail "vsubst: type mismatch"))))
(defun vsubst* (theta tm)
  (cond
    ((hvar-p tm) (let ((p (assoc tm theta :test #'term=))) (if p (cdr p) tm)))
    ((hconst-p tm) tm)
    ((hcomb-p tm) (make-hcomb (vsubst* theta (hcomb-rator tm)) (vsubst* theta (hcomb-rand tm))))
    ((habs-p tm)
     (let* ((v (habs-bv tm))
            (theta2 (remove v theta :key #'car :test #'term=)))
       (if (null theta2) tm
           (let ((s2 (vsubst* theta2 (habs-body tm))))
             (if (some (lambda (p) (and (vfree-in v (cdr p)) (vfree-in (car p) (habs-body tm)))) theta2)
                 (let ((v2 (variant (list s2) v)))
                   (make-habs v2 (vsubst* (acons v v2 theta2) (habs-body tm))))
                 (make-habs v s2))))))))
(defun vsubst (theta tm)
  (if (null theta) tm (progn (vsubst-typecheck theta) (vsubst* theta tm))))

;;; type instantiation in a term, with bound-variable renaming to avoid capture.
(define-condition clash (error) ((w :initarg :w :reader clash-w)))
(defun inst* (env tyin tm)
  (cond
    ((hvar-p tm)
     (let* ((ty2 (type-subst tyin (hvar-ty tm)))
            (tm2 (if (type= ty2 (hvar-ty tm)) tm (make-hvar (hvar-name tm) ty2)))
            (found (rassoc tm2 env :test #'term=)))
       (cond ((null found) tm2)
             ((term= (car found) tm) tm2)
             (t (error 'clash :w tm2)))))
    ((hconst-p tm) (make-hconst (hconst-name tm) (type-subst tyin (hconst-ty tm))))
    ((hcomb-p tm) (make-hcomb (inst* env tyin (hcomb-rator tm)) (inst* env tyin (hcomb-rand tm))))
    ((habs-p tm)
     (let* ((y (habs-bv tm)) (y2 (inst* '() tyin y)))
       (handler-case
           (make-habs y2 (inst* (acons y y2 env) tyin (habs-body tm)))
         (clash (c)
           (unless (term= (clash-w c) y2) (error c))
           (let* ((ifrees (mapcar (lambda (f) (inst* '() tyin f)) (frees (habs-body tm))))
                  (y3 (variant ifrees y2))
                  (z (make-hvar (hvar-name y3) (hvar-ty y))))
             (inst* env tyin (make-habs z (vsubst (list (cons y z)) (habs-body tm)))))))))))
(defun inst-term (tyin tm) (if (null tyin) tm (inst* '() tyin tm)))

;;; smart constructors (well-typed-by-construction)
(defun mk-var (name ty) (make-hvar name ty))
(defun mk-const (name &optional (tyin '()))   ; tyin: alist (tyvar-name . htype)
  (make-hconst name (type-subst tyin (get-const-type name))))
(defun mk-comb (f a)
  (let ((tf (type-of f)))
    (unless (and (htapp-p tf) (string= (htapp-op tf) "fun")
                 (type= (first (htapp-args tf)) (type-of a)))
      (kfail "mk-comb: types do not agree"))
    (make-hcomb f a)))
(defun mk-abs (v b) (unless (hvar-p v) (kfail "mk-abs: bound is not a var")) (make-habs v b))
(defun list-mk-comb (f args) (reduce #'mk-comb args :initial-value f))
(defun list-mk-abs (vs b) (reduce (lambda (v acc) (mk-abs v acc)) vs :from-end t :initial-value b))

(defun rator (tm) (if (hcomb-p tm) (hcomb-rator tm) (kfail "rator")))
(defun rand  (tm) (if (hcomb-p tm) (hcomb-rand tm)  (kfail "rand")))
(defun dest-comb (tm) (if (hcomb-p tm) (values (hcomb-rator tm) (hcomb-rand tm)) (kfail "dest-comb")))
(defun dest-abs  (tm) (if (habs-p tm)  (values (habs-bv tm) (habs-body tm)) (kfail "dest-abs")))

(defun mk-eq (l r)
  (let ((ty (type-of l)))
    (unless (type= ty (type-of r)) (kfail "mk-eq: sides differ in type"))
    (mk-comb (mk-comb (mk-const "=" (list (cons "A" ty))) l) r)))
(defun is-eq (tm)
  (and (hcomb-p tm) (hcomb-p (hcomb-rator tm))
       (let ((c (hcomb-rator (hcomb-rator tm))))
         (and (hconst-p c) (string= (hconst-name c) "=")))))
(defun dest-eq (tm)
  (unless (is-eq tm) (kfail "dest-eq: not an equation: ~a" tm))
  (values (hcomb-rand (hcomb-rator tm)) (hcomb-rand tm)))

;;; ----------------------------------------------------------------------------
;;; THE OPAQUE THEOREM TYPE.
;;; %make-thm is NOT exported. Only the rules below may call it.
;;; A thm is a sequent: a list of hypotheses (bool terms) entailing a conclusion.
;;; ----------------------------------------------------------------------------

(defstruct (thm (:constructor %make-thm (hyp concl)) (:predicate thm-p))
  hyp concl)
(defun hyp   (th) (thm-hyp th))
(defun concl (th) (thm-concl th))

(defun term-union (l1 l2) (dolist (x l1 l2) (unless (member x l2 :test #'aconv) (push x l2))))
(defun term-remove (x l) (remove x l :test #'aconv))

;;; ---- the ten primitive inference rules (the entire trust surface) ----------

;; 1.  |- t = t
(defun prim-refl (tm) (%make-thm '() (mk-eq tm tm)))

;; 2.  A|-s=m   B|-m=t   -->   A,B |- s=t
(defun prim-trans (th1 th2)
  (multiple-value-bind (l m1) (dest-eq (concl th1))
    (multiple-value-bind (m2 r) (dest-eq (concl th2))
      (unless (aconv m1 m2) (kfail "TRANS: middle terms differ"))
      (%make-thm (term-union (hyp th1) (hyp th2)) (mk-eq l r)))))

;; 3.  A|-f=g   B|-x=y   -->   A,B |- f x = g y
(defun prim-mk-comb (th1 th2)
  (multiple-value-bind (f g) (dest-eq (concl th1))
    (multiple-value-bind (x y) (dest-eq (concl th2))
      (%make-thm (term-union (hyp th1) (hyp th2)) (mk-eq (mk-comb f x) (mk-comb g y))))))

;; 4.  A|-s=t  (x not free in A)  -->  A |- (\x.s) = (\x.t)
(defun prim-abs (v th)
  (unless (hvar-p v) (kfail "ABS: not a var"))
  (when (some (lambda (h) (vfree-in v h)) (hyp th)) (kfail "ABS: var free in hypotheses"))
  (multiple-value-bind (s tt) (dest-eq (concl th))
    (%make-thm (hyp th) (mk-eq (mk-abs v s) (mk-abs v tt)))))

;; 5.  |- (\x.t) x = t
(defun prim-beta (tm)
  (unless (and (hcomb-p tm) (habs-p (hcomb-rator tm))) (kfail "BETA: not a redex"))
  (let* ((ab (hcomb-rator tm)) (arg (hcomb-rand tm)))
    (unless (term= arg (habs-bv ab)) (kfail "BETA: arg is not the bound variable"))
    (%make-thm '() (mk-eq tm (habs-body ab)))))

;; 6.  {p} |- p   (p : bool)
(defun prim-assume (tm)
  (unless (type= (type-of tm) (bool-ty)) (kfail "ASSUME: not boolean"))
  (%make-thm (list tm) tm))

;; 7.  A|-p=q   B|-p   -->   A,B |- q
(defun prim-eq-mp (th1 th2)
  (multiple-value-bind (p q) (dest-eq (concl th1))
    (unless (aconv p (concl th2)) (kfail "EQ_MP: antecedent mismatch"))
    (%make-thm (term-union (hyp th1) (hyp th2)) q)))

;; 8.  A|-p   B|-q   -->   (A\{q}) , (B\{p}) |- p=q
(defun prim-deduct (th1 th2)
  (let ((p (concl th1)) (q (concl th2)))
    (%make-thm (term-union (term-remove q (hyp th1)) (term-remove p (hyp th2)))
               (mk-eq p q))))

;; 9.  instantiate term variables.  theta: alist (var . term)
(defun prim-inst (theta th)
  (%make-thm (mapcar (lambda (h) (vsubst theta h)) (hyp th))
             (vsubst theta (concl th))))

;; 10.  instantiate type variables.  tyin: alist (tyvar-name . htype)
(defun prim-inst-type (tyin th)
  (%make-thm (mapcar (lambda (h) (inst-term tyin h)) (hyp th))
             (inst-term tyin (concl th))))

;;; ----------------------------------------------------------------------------
;;; DEFINITIONAL EXTENSION (still part of the trusted base).
;;; ----------------------------------------------------------------------------

(defvar *axioms* '())
(defun new-axiom (tm)
  (unless (type= (type-of tm) (bool-ty)) (kfail "new-axiom: not boolean"))
  (let ((th (%make-thm '() tm))) (push th *axioms*) th))
(defun axioms () *axioms*)

(defvar *definitions* '())
;; introduce a new constant c with |- c = rhs, for closed rhs whose tyvars occur in c's type.
(defun new-basic-definition (tm)
  (multiple-value-bind (lhs rhs) (dest-eq tm)
    (unless (hvar-p lhs) (kfail "definition: lhs must be a variable"))
    (when (frees rhs) (kfail "definition: rhs not closed: free ~a" (mapcar #'hvar-name (frees rhs))))
    (let ((cname (hvar-name lhs)) (cty (hvar-ty lhs)))
      (unless (subsetp (type-vars rhs) (type-vars cty) :test #'string=)
        (kfail "definition: rhs has type vars not in constant type"))
      (declare-const cname cty)
      (let ((th (%make-thm '() (mk-eq (make-hconst cname cty) rhs))))
        (push (cons cname th) *definitions*) th))))
(defun definitions () *definitions*)
