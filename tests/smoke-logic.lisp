;;;; Prove genuine theorems using only derived rules (which bottom out in the
;;;; 10 kernel primitives). If these certify, the logic layer is sound & usable.
(load (merge-pathnames "../src/kernel.lisp" *load-pathname*))
(load (merge-pathnames "../src/logic.lisp" *load-pathname*))
(in-package :mccarthy)

(defvar *pass* 0) (defvar *fail* 0)
(defmacro check (name form)
  `(handler-case (if ,form (progn (incf *pass*) (format t "  ok   ~a~%" ,name))
                     (progn (incf *fail*) (format t "  FAIL ~a~%" ,name)))
     (error (e) (incf *fail*) (format t "  FAIL ~a  [~a]~%" ,name e))))

(format t "~%=== logic smoke test ===~%")
(defparameter *b* (bool))
(defparameter *p* (mk-var "p" *b*))
(defparameter *q* (mk-var "q" *b*))

;; 1. TRUTH
(check "|- T  (no hyps)" (and (null (hyp (truth)))
                              (hconst-p (concl (truth)))
                              (string= (hconst-name (concl (truth))) "T")))

;; 2. CONJ then project back
(defparameter *pq* (conj (assume *p*) (assume *q*)))   ; {p,q} |- p/\q
(check "CONJ: {p,q} |- p/\\q" (is-conj (concl *pq*)))
(check "CONJUNCT1 recovers p" (aconv (concl (conjunct1 *pq*)) *p*))
(check "CONJUNCT2 recovers q" (aconv (concl (conjunct2 *pq*)) *q*))

;; 3. |- p /\ q ==> q /\ p     (a real propositional theorem, hypothesis-free)
(defparameter *swap*
  (let* ((th0 (assume (mk-conj *p* *q*)))           ; {p/\q} |- p/\q
         (a (conjunct1 th0)) (b (conjunct2 th0))    ; {p/\q}|- p ; {p/\q}|- q
         (qp (conj b a)))                            ; {p/\q}|- q/\p
    (disch (mk-conj *p* *q*) qp)))                   ; |- (p/\q) ==> (q/\p)
(check "|- (p/\\q) ==> (q/\\p)  is hypothesis-free"
       (and (null (hyp *swap*)) (is-imp (concl *swap*))))
(check "  ...and its shape is correct"
       (multiple-value-bind (l r) (dest-imp (concl *swap*))
         (and (is-conj l) (is-conj r)
              (multiple-value-bind (rl rr) (dest-conj r) (and (aconv rl *q*) (aconv rr *p*))))))
(format t "    ~a~%" (thm->sexp *swap*))

;; 4. MP works: from |- (p/\q)==>(q/\p) and |- p/\q derive |- q/\p
(check "MP: detach q/\\p"
       (let ((res (mp *swap* (conj (assume *p*) (assume *q*)))))
         (is-conj (concl res))))

;; 5. universal quantifier:  |- !x. x = x
(defparameter *A* (a-ty))
(defparameter *x* (mk-var "x" *A*))
(defparameter *allrefl* (gen *x* (refl *x*)))         ; |- !x. x=x
(check "|- !x. x=x" (and (null (hyp *allrefl*)) (is-forall (concl *allrefl*))))
(format t "    ~a~%" (thm->sexp *allrefl*))

;; 6. SPEC:  from |- !x. x=x  derive  |- c=c
(defparameter *c* (mk-var "c" *A*))
(check "SPEC !x.x=x at c gives c=c"
       (let ((sp (spec *c* *allrefl*)))
         (multiple-value-bind (l r) (dest-eq (concl sp)) (and (aconv l *c*) (aconv r *c*)))))

;; 7. universal modus ponens:  |- (!x. P x) ==> P c    (with P a free predicate)
(defparameter *Pty* (mk-fun *A* *b*))
(defparameter *P* (mk-var "P" *Pty*))
(defparameter *umpp*
  (let* ((allP (mk-forall *x* (mk-comb *P* *x*)))      ; !x. P x
         (th (assume allP))                             ; {!x.Px} |- !x.Px
         (pc (spec *c* th)))                            ; {!x.Px} |- P c
    (disch allP pc)))                                   ; |- (!x.Px) ==> P c
(check "|- (!x. P x) ==> P c  is hypothesis-free"
       (and (null (hyp *umpp*)) (is-imp (concl *umpp*))))
(format t "    ~a~%" (thm->sexp *umpp*))

;; 8. beta reduction certified:  |- (\x. f x) c = f c
(defparameter *f* (mk-var "f" (mk-fun *A* *A*)))
(check "beta-rule: (\\x. f x) c reduces to f c"
       (let* ((tm (mk-comb (mk-abs *x* (mk-comb *f* *x*)) *c*))
              (th (beta-conv tm)))
         (aconv (nth-value 1 (dest-eq (concl th))) (mk-comb *f* *c*))))

(format t "~%=== ~a passed, ~a failed ===~%" *pass* *fail*)
(if (zerop *fail*) (sb-ext:exit :code 0) (sb-ext:exit :code 1))
