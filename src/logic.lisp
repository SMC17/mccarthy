;;;; src/logic.lisp — UNTRUSTED logic layer.
;;;;
;;;; Everything here is derived solely from the ten kernel primitives, so it
;;;; cannot introduce unsoundness no matter what bugs it contains: a wrong
;;;; derivation simply fails to produce the theorem you wanted. This file adds:
;;;;   * conversion combinators (rewriting infrastructure) + beta reduction
;;;;   * the logical connectives  T  /\  ==>  !  by definitional extension
;;;;   * the standard natural-deduction rules derived over them
;;;;   * an s-expression printer
;;;; Mirrors John Harrison's HOL Light `equal.ml` / `bool.ml`.

(defpackage :mccarthy
  (:use :cl :mccarthy.kernel)
  (:shadowing-import-from :mccarthy.kernel #:type-of #:abs)
  (:export
   ;; thin kernel aliases
   #:refl #:trans #:mk-comb-thm #:abs-thm #:beta-thm #:assume #:eq-mp
   #:deduct #:inst-thm #:inst-type-thm
   ;; derived rules
   #:ap-term #:ap-thm #:sym #:add-assum #:prove-hyp
   #:beta-conv #:depth-conv #:conv-rule #:beta-rule
   #:all-conv #:no-conv #:then-conv #:orelse-conv #:try-conv #:conv-fail
   #:truth #:eqt-intro #:eqt-elim
   #:conj #:conjunct1 #:conjunct2 #:mp #:disch #:undisch #:gen #:spec
   ;; connective term constructors / destructors
   #:bool #:mk-t #:mk-conj #:mk-imp #:mk-forall
   #:dest-conj #:dest-imp #:dest-forall #:is-conj #:is-imp #:is-forall
   ;; printing
   #:pp #:thm->sexp #:print-thm))

(in-package :mccarthy)

;;; thin aliases over the kernel rules (kernel rule symbols are |REFL| etc.)
(declaim (inline refl trans mk-comb-thm abs-thm beta-thm assume eq-mp deduct inst-thm inst-type-thm))
(defun refl (tm) (prim-refl tm))
(defun trans (a b) (prim-trans a b))
(defun mk-comb-thm (a b) (prim-mk-comb a b))
(defun abs-thm (v th) (prim-abs v th))
(defun beta-thm (tm) (prim-beta tm))
(defun assume (tm) (prim-assume tm))
(defun eq-mp (a b) (prim-eq-mp a b))
(defun deduct (a b) (prim-deduct a b))
(defun inst-thm (theta th) (prim-inst theta th))
(defun inst-type-thm (tyin th) (prim-inst-type tyin th))

(defun bool () (bool-ty))

;;; ---- basic derived equality rules -----------------------------------------

;; |- x=y  -->  |- f x = f y
(defun ap-term (f th) (mk-comb-thm (refl f) th))
;; |- f=g  -->  |- f x = g x
(defun ap-thm (th x) (mk-comb-thm th (refl x)))

;; |- s=t  -->  |- t=s
(defun sym (th)
  (let* ((c (concl th)) (eqop (hcomb-rator (hcomb-rator c))))
    (multiple-value-bind (l r) (dest-eq c) (declare (ignore r))
      (eq-mp (ap-thm (ap-term eqop th) l) (refl l)))))

;; add a hypothesis:  A|-p  -->  A,a |- p
(defun add-assum (a th) (eq-mp (sym (deduct (assume a) th)) (assume a)))

;; discharge a proved hypothesis: if (concl ath) is among hyps of bth, remove it.
(defun prove-hyp (ath bth)
  (if (member (concl ath) (hyp bth) :test #'aconv)
      (eq-mp (deduct ath bth) ath)
      bth))

;;; ---- conversion combinators ------------------------------------------------
;;; A "conversion" maps a term TM to a theorem  |- TM = TM'.

(define-condition conv-fail (error) ())
(defun all-conv (tm) (refl tm))
(defun no-conv (tm) (declare (ignore tm)) (error 'conv-fail))

(defun then-conv (c1 c2)
  (lambda (tm)
    (let ((th1 (funcall c1 tm)))
      (multiple-value-bind (l r) (dest-eq (concl th1)) (declare (ignore l))
        (let ((th2 (funcall c2 r)))
          (if (term= (nth-value 0 (dest-eq (concl th2)))
                     (nth-value 1 (dest-eq (concl th2))))
              th1 (trans th1 th2)))))))
(defun orelse-conv (c1 c2)
  (lambda (tm) (handler-case (funcall c1 tm) (conv-fail () (funcall c2 tm)))))
(defun try-conv (c) (orelse-conv c #'all-conv))

(defun conv-or-refl (c tm) (handler-case (funcall c tm) (conv-fail () (refl tm))))

;; beta:  (\v. body) arg  =  body[arg/v]   (arg arbitrary)
(defun beta-conv (tm)
  (unless (and (hcomb-p tm) (habs-p (hcomb-rator tm))) (error 'conv-fail))
  (let* ((ab (hcomb-rator tm)) (arg (hcomb-rand tm)) (v (habs-bv ab)))
    (if (term= arg v)
        (beta-thm tm)
        (inst-thm (list (cons v arg)) (beta-thm (mk-comb ab v))))))

;; recurse a conversion into immediate subterms
(defun sub-conv (c tm)
  (cond ((hcomb-p tm)
         (mk-comb-thm (conv-or-refl c (hcomb-rator tm))
                      (conv-or-refl c (hcomb-rand tm))))
        ((habs-p tm) (abs-thm (habs-bv tm) (conv-or-refl c (habs-body tm))))
        (t (refl tm))))

;; bottom-up repeated application
(defun depth-conv (c)
  (labels ((dc (tm)
             (let* ((th1 (sub-conv #'dc tm))
                    (r (nth-value 1 (dest-eq (concl th1)))))
               (handler-case
                   (let* ((th2 (funcall c r))
                          (r2 (nth-value 1 (dest-eq (concl th2)))))
                     (trans (trans th1 th2) (dc r2)))
                 (conv-fail () th1)))))
    #'dc))

(defun conv-rule (c th) (eq-mp (funcall c (concl th)) th))
(defun beta-rule (th) (conv-rule (depth-conv #'beta-conv) th))

;;; ---- the logical connectives, by definitional extension --------------------

(defvar *T-def*) (defvar *and-def*) (defvar *imp-def*) (defvar *forall-def*)
(defvar *truth*)

(defun init-logic ()
  (let* ((b (bool))
         (bbb (mk-fun b (mk-fun b b))))
    ;; T = ((\p.p) = (\p.p))
    (let* ((p (mk-var "p" b)) (lam (mk-abs p p)))
      (setf *T-def* (new-basic-definition (mk-eq (mk-var "T" b) (mk-eq lam lam))))
      (setf *truth* (eq-mp (sym *T-def*) (refl lam))))
    ;; /\ = \p q. (\f. f p q) = (\f. f T T)
    (let* ((p (mk-var "p" b)) (q (mk-var "q" b)) (f (mk-var "f" bbb)) (tc (mk-t))
           (lhs (mk-abs f (mk-comb (mk-comb f p) q)))
           (rhs (mk-abs f (mk-comb (mk-comb f tc) tc)))
           (def (mk-abs p (mk-abs q (mk-eq lhs rhs)))))
      (setf *and-def* (new-basic-definition (mk-eq (mk-var "/\\" bbb) def))))
    ;; ==> = \p q. (p /\ q) = p
    (let* ((p (mk-var "p" b)) (q (mk-var "q" b))
           (def (mk-abs p (mk-abs q (mk-eq (mk-conj p q) p)))))
      (setf *imp-def* (new-basic-definition (mk-eq (mk-var "==>" bbb) def))))
    ;; ! = \P:A->bool. P = \x. T
    (let* ((aty (a-ty)) (pty (mk-fun aty b)) (pp (mk-var "P" pty)) (x (mk-var "x" aty))
           (def (mk-abs pp (mk-eq pp (mk-abs x (mk-t)))))
           (allty (mk-fun pty b)))
      (setf *forall-def* (new-basic-definition (mk-eq (mk-var "!" allty) def))))))

;;; connective term builders / destructors
(defun mk-t () (mk-const "T"))
(defun mk-conj (p q) (list-mk-comb (mk-const "/\\") (list p q)))
(defun mk-imp  (p q) (list-mk-comb (mk-const "==>") (list p q)))
(defun mk-forall (x body) (mk-comb (mk-const "!" (list (cons "A" (hvar-ty x)))) (mk-abs x body)))

(defun head-const-name (tm)
  (let ((h tm)) (loop while (hcomb-p h) do (setf h (hcomb-rator h)))
    (and (hconst-p h) (hconst-name h))))
(defun is-conj (tm) (and (hcomb-p tm) (hcomb-p (hcomb-rator tm))
                         (equal (head-const-name tm) "/\\")))
(defun is-imp  (tm) (and (hcomb-p tm) (hcomb-p (hcomb-rator tm))
                         (equal (head-const-name tm) "==>")))
(defun is-forall (tm) (and (hcomb-p tm) (equal (head-const-name tm) "!")
                           (habs-p (hcomb-rand tm))))
(defun dest-conj (tm) (unless (is-conj tm) (error "dest-conj"))
  (values (hcomb-rand (hcomb-rator tm)) (hcomb-rand tm)))
(defun dest-imp (tm) (unless (is-imp tm) (error "dest-imp"))
  (values (hcomb-rand (hcomb-rator tm)) (hcomb-rand tm)))
(defun dest-forall (tm) (unless (is-forall tm) (error "dest-forall"))
  (let ((lam (hcomb-rand tm))) (values (habs-bv lam) (habs-body lam))))

;;; ---- derived natural-deduction rules ---------------------------------------

(defun truth () *truth*)

;; |- p   -->   |- p = T
(defun eqt-intro (th) (deduct th (truth)))
;; |- p = T   -->   |- p
(defun eqt-elim (th) (eq-mp (sym th) (truth)))

;; |- p ,  |- q   -->   |- p /\ q
(defun conj (th1 th2)
  (let* ((p (concl th1)) (q (concl th2))
         (b (bool)) (bbb (mk-fun b (mk-fun b b)))
         (avoid (free-vars-list (list* p q (append (hyp th1) (hyp th2)))))
         (f (variant avoid (mk-var "f" bbb)))
         (and-eq (beta-rule (ap-thm (ap-thm *and-def* p) q)))   ; |- (p/\q) = ((\f.fpq)=(\f.fTT))
         (step1 (ap-term f (eqt-intro th1)))                    ; |- f p = f T
         (step2 (mk-comb-thm step1 (eqt-intro th2)))            ; |- (f p) q = (f T) T
         (absf  (abs-thm f step2)))                             ; |- (\f.fpq)=(\f.fTT)
    (eq-mp (sym and-eq) absf)))

(defun %conjunct (th which)
  (multiple-value-bind (p q) (dest-conj (concl th))
    (let* ((b (bool))
           (and-eq (beta-rule (ap-thm (ap-thm *and-def* p) q)))
           (th2 (eq-mp and-eq th))                              ; |- (\f.fpq)=(\f.fTT)
           (a (mk-var "a" b)) (c (mk-var "c" b))
           (sel (if (eq which :left) (mk-abs a (mk-abs c a)) (mk-abs a (mk-abs c c))))
           (th4 (beta-rule (ap-thm th2 sel))))                  ; |- p=T  (or q=T)
      (eqt-elim th4))))
(defun conjunct1 (th) (%conjunct th :left))
(defun conjunct2 (th) (%conjunct th :right))

;; |- p==>q ,  |- p   -->   |- q
(defun mp (thi thp)
  (multiple-value-bind (p q) (dest-imp (concl thi))
    (let* ((imp-eq (beta-rule (ap-thm (ap-thm *imp-def* p) q)))  ; |- (p==>q)=((p/\q)=p)
           (th2 (eq-mp imp-eq thi))                              ; |- (p/\q)=p
           (th3 (eq-mp (sym th2) thp)))                          ; |- p/\q
      (conjunct2 th3))))

;; a |- ... ,  th: A|-t   -->   A |- a==>t
(defun disch (a th)
  (let* ((tt (concl th))
         (th1 (conj (assume a) th))                  ; {a}∪A |- a/\t
         (th2 (conjunct1 (assume (concl th1))))      ; {a/\t} |- a
         (th3 (deduct th1 th2))                      ; A |- (a/\t)=a
         (imp-eq (beta-rule (ap-thm (ap-thm *imp-def* a) tt)))) ; |- (a==>t)=((a/\t)=a)
    (eq-mp (sym imp-eq) th3)))

;; |- p==>q   -->   {p}|- q
(defun undisch (th)
  (multiple-value-bind (p q) (dest-imp (concl th)) (declare (ignore q))
    (mp th (assume p))))

;; A|-p  (x not free in A)  -->  A |- !x.p
(defun gen (x th)
  (let* ((p (concl th))
         (abs1 (abs-thm x (eqt-intro th)))           ; A |- (\x.p)=(\x.T)
         (lam (mk-abs x p))
         (fdef (inst-type-thm (list (cons "A" (hvar-ty x))) *forall-def*))
         (th1 (beta-rule (ap-thm fdef lam))))        ; |- (!(\x.p)) = ((\x.p)=(\x.T))
    (eq-mp (sym th1) abs1)))

;; |- !x.p   -->   |- p[tm/x]
(defun spec (tm th)
  (let* ((pred (hcomb-rand (concl th)))               ; \x.p
         (ty (hvar-ty (habs-bv pred)))
         (fdef (inst-type-thm (list (cons "A" ty)) *forall-def*))
         (th1 (beta-rule (ap-thm fdef pred)))         ; |- (!pred) = (pred=\x.T)
         (th2 (eq-mp th1 th))                         ; |- pred = \x.T
         (th3 (beta-rule (ap-thm th2 tm))))           ; |- p[tm/x] = T
    (eqt-elim th3)))

;;; ---- s-expression printer --------------------------------------------------

(defun sym* (s) (intern (string-upcase s) :keyword))
(defun pp (tm)
  "Render a term as a readable s-expression."
  (cond
    ((hvar-p tm) (intern (hvar-name tm) :keyword))
    ((hconst-p tm) (intern (hconst-name tm) :keyword))
    ((and (is-eq tm)) (multiple-value-bind (l r) (dest-eq tm) (list := (pp l) (pp r))))
    ((is-conj tm) (multiple-value-bind (l r) (dest-conj tm) (list :/\\ (pp l) (pp r))))
    ((is-imp tm)  (multiple-value-bind (l r) (dest-imp tm)  (list :==> (pp l) (pp r))))
    ((is-forall tm) (multiple-value-bind (x b) (dest-forall tm) (list :! (intern (hvar-name x) :keyword) (pp b))))
    ((hcomb-p tm) (list (pp (hcomb-rator tm)) (pp (hcomb-rand tm))))
    ((habs-p tm) (list :lam (intern (hvar-name (habs-bv tm)) :keyword) (pp (habs-body tm))))))
(defun thm->sexp (th)
  (list (mapcar #'pp (hyp th)) '|-| (pp (concl th))))
(defun print-thm (th &optional (stream *standard-output*))
  (let ((h (hyp th)))
    (format stream "~{~a~^, ~} |- ~a~%"
            (mapcar (lambda (x) (pp-string x)) h) (pp-string (concl th)))))
(defun pp-string (tm) (format nil "~a" (pp tm)))

(init-logic)
