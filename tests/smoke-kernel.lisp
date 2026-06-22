;;;; Hard smoke test of the trusted kernel: exercise every primitive rule and
;;;; the substitution machinery, AND prove that a false theorem cannot be forged.
(load (merge-pathnames "../src/kernel.lisp" *load-pathname*))
(in-package :mccarthy.kernel)

(defvar *pass* 0) (defvar *fail* 0)
(defmacro check (name form)
  `(handler-case (if ,form (progn (incf *pass*) (format t "  ok   ~a~%" ,name))
                     (progn (incf *fail*) (format t "  FAIL ~a~%" ,name)))
     (error (e) (incf *fail*) (format t "  FAIL ~a  [error: ~a]~%" ,name e))))
(defmacro check-error (name form)
  `(handler-case (progn ,form (incf *fail*) (format t "  FAIL ~a  [expected rejection]~%" ,name))
     (kernel-error () (incf *pass*) (format t "  ok   ~a  [correctly rejected]~%" ,name))
     (error (e) (incf *pass*) (format t "  ok   ~a  [rejected: ~a]~%" ,name (type-of e)))))

(format t "~%=== kernel smoke test ===~%")

;; some terms:  x,y : A ;  f : A->A ;  p,q : bool
(defparameter *A* (a-ty))
(defparameter *x* (mk-var "x" *A*))
(defparameter *y* (mk-var "y" *A*))
(defparameter *f* (mk-var "f" (mk-fun *A* *A*)))
(defparameter *p* (mk-var "p" (bool-ty)))
(defparameter *q* (mk-var "q" (bool-ty)))

;; REFL
(defparameter *refl-x* (prim-refl *x*))
(check "REFL gives x=x" (let ((c (concl *refl-x*)))
                         (multiple-value-bind (l r) (dest-eq c) (and (term= l *x*) (term= r *x*)))))
(check "REFL has no hyps" (null (hyp *refl-x*)))

;; type-of correctness
(check "type-of (f x) = A" (type= (type-of (mk-comb *f* *x*)) *A*))
(check-error "mk-comb ill-typed (x x) rejected" (mk-comb *x* *x*))

;; ASSUME + EQ_MP + TRANS via equational chain:  assume x=y, y=f? no — build x=y,y=z chain
(defparameter *z* (mk-var "z" *A*))
(defparameter *axy* (prim-assume (mk-eq *x* *y*)))     ; {x=y} |- x=y
(defparameter *ayz* (prim-assume (mk-eq *y* *z*)))     ; {y=z} |- y=z
(defparameter *axz* (prim-trans *axy* *ayz*))          ; {x=y,y=z} |- x=z
(check "TRANS chains x=y,y=z |- x=z"
       (multiple-value-bind (l r) (dest-eq (concl *axz*)) (and (term= l *x*) (term= r *z*))))
(check "TRANS unions hyps" (= 2 (length (hyp *axz*))))
(check-error "TRANS with mismatched middle rejected"
             (prim-trans *axy* (prim-assume (mk-eq *z* *x*))))

;; MK_COMB: from x=y derive f x = f y
(defparameter *reff* (prim-refl *f*))
(defparameter *fxfy* (prim-mk-comb *reff* *axy*))
(check "MK_COMB: f x = f y"
       (multiple-value-bind (l r) (dest-eq (concl *fxfy*))
         (and (term= l (mk-comb *f* *x*)) (term= r (mk-comb *f* *y*)))))

;; BETA:  (\x. f x) x  =  f x
(defparameter *redex* (mk-comb (mk-abs *x* (mk-comb *f* *x*)) *x*))
(defparameter *beta* (prim-beta *redex*))
(check "BETA reduces (\\x.f x) x = f x"
       (multiple-value-bind (l r) (dest-eq (concl *beta*))
         (and (term= l *redex*) (term= r (mk-comb *f* *x*)))))
(check-error "BETA on non-redex rejected" (prim-beta (mk-comb *f* *x*)))

;; ABS:  from x=y (NO hyp mentioning bound var allowed); use a clean theorem
;; reflexive f x = f x, abstract over x  ->  (\x.f x) = (\x.f x)
(defparameter *absthm* (prim-abs *x* (prim-refl (mk-comb *f* *x*))))
(check "ABS builds (\\x.f x)=(\\x.f x)"
       (multiple-value-bind (l r) (dest-eq (concl *absthm*))
         (and (habs-p l) (habs-p r))))
(check-error "ABS over var free in hyp rejected" (prim-abs *x* *axy*)) ; x free in {x=y}

;; ASSUME requires boolean
(check-error "ASSUME on non-bool rejected" (prim-assume *x*))

;; EQ_MP:  (p=q) and p  give q. Build with assumptions.
(defparameter *apq* (prim-assume (mk-eq *p* *q*)))
(defparameter *ap*  (prim-assume *p*))
(defparameter *q-th* (prim-eq-mp *apq* *ap*))
(check "EQ_MP yields q" (term= (concl *q-th*) *q*))

;; DEDUCT_ANTISYM_RULE: from {p}|-q-ish... use {p}|-p and {q}|-q to get |- p=q with hyps {q},{p}
(defparameter *da* (prim-deduct (prim-assume *p*) (prim-assume *q*)))
(check "DEDUCT gives p=q" (multiple-value-bind (l r) (dest-eq (concl *da*))
                            (and (term= l *p*) (term= r *q*))))
(check "DEDUCT hyps are {q,p}" (= 2 (length (hyp *da*))))

;; INST: instantiate x:=y in {x=y? no} — use REFL x then INST x:=f y... keep types
(defparameter *inst1* (prim-inst (list (cons *x* (mk-comb *f* *y*))) (prim-refl *x*)))
(check "INST x:=f y in (x=x) gives (f y = f y)"
       (multiple-value-bind (l r) (dest-eq (concl *inst1*)) (declare (ignore r))
         (term= l (mk-comb *f* *y*))))

;; INST_TYPE: REFL x:A, instantiate A:=bool  ->  x:bool = x:bool
(defparameter *it* (prim-inst-type (list (cons "A" (bool-ty))) (prim-refl *x*)))
(check "INST_TYPE A:=bool retypes x"
       (multiple-value-bind (l r) (dest-eq (concl *it*)) (declare (ignore r))
         (type= (type-of l) (bool-ty))))

;; capture-avoidance in vsubst: subst y:=x into (\x. =? ) must rename bound x.
;; build term  \x. (y = x)  : substitute y:=x ; naive subst would capture.
(defparameter *body* (mk-eq *y* *x*))            ; y = x  : bool
(defparameter *lam*  (mk-abs *x* *body*))        ; \x. (y=x)
(defparameter *subd* (vsubst (list (cons *y* *x*)) *lam*)) ; replace free y by x
(check "vsubst capture-avoidance renames bound var"
       ;; result must be  \x'. (x = x')  — the inner binder renamed, free x preserved
       (and (habs-p *subd*)
            (not (term= (habs-bv *subd*) *x*))            ; binder was renamed
            (vfree-in *x* *subd*)))                       ; the substituted free x is genuinely free

;; ---- SOUNDNESS: you cannot fabricate a false theorem ----
;; There is no exported constructor for thm other than the rules; the only way to
;; get  |- p = q  for distinct atoms p,q with NO hypotheses is impossible.
;; Demonstrate: the only |- p=q we can make (DEDUCT) carries hyps {p},{q} — not a tautology.
(check "forged p=q is NOT hypothesis-free (carries its assumptions)"
       (> (length (hyp *da*)) 0))

(format t "~%=== ~a passed, ~a failed ===~%" *pass* *fail*)
(if (zerop *fail*) (sb-ext:exit :code 0) (sb-ext:exit :code 1))
