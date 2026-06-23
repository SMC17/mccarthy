;;;; Disjunction / negation / falsity — all proved through axiom-free definitions.
(load (merge-pathnames "../src/load.lisp" *load-pathname*))
(in-package :mccarthy)

(defvar *pass* 0) (defvar *fail* 0)
(defun prove! (name sig goal &optional (depth 18))
  (multiple-value-bind (th g) (prove-sexp sig goal :depth depth)
    (cond ((and th (aconv (concl th) g) (null (hyp th)))
           (incf *pass*) (format t "  PROVED  ~a~%            ~a~%" name (pp (concl th))))
          (t (incf *fail*) (format t "  FAILED  ~a~%" name)))))
(defun refute! (name sig goal &optional (depth 14))
  (multiple-value-bind (th g) (prove-sexp sig goal :depth depth) (declare (ignore g))
    (cond (th (incf *fail*) (format t "  UNSOUND ~a~%" name))
          (t (incf *pass*) (format t "  rejected ~a~%" name)))))

(format t "~%=== disjunction / negation ===~%")

(prove! "disj intro  p -> (p \\/ q)" '((p bool) (q bool)) '(==> p (or p q)))
(prove! "disj commutes  (p \\/ q) -> (q \\/ p)" '((p bool) (q bool))
        '(==> (or p q) (or q p)))
(prove! "disj elimination  (p\\/q)->(p->r)->(q->r)->r" '((p bool) (q bool) (r bool))
        '(==> (or p q) (==> (==> p r) (==> (==> q r) r))))
(prove! "contrapositive  (p->q) -> (~q -> ~p)" '((p bool) (q bool))
        '(==> (==> p q) (==> (not q) (not p))))
(prove! "double-negation intro  p -> ~~p" '((p bool)) '(==> p (not (not p))))
(prove! "non-contradiction  ~(p /\\ ~p)" '((p bool)) '(not (and p (not p))))
(prove! "ex falso  F -> p" '((p bool)) '(==> F p))
(prove! "disj with quantifier  (!x.P x) -> (P c \\/ Q c)"
        '((p (fun a bool)) (q (fun a bool)) (c a))
        '(==> (! (x a) (p x)) (or (p c) (q c))))

;; soundness — classically-tempting non-theorems must be refused
(refute! "p \\/ q  alone is NOT valid" '((p bool) (q bool)) '(or p q))
(refute! "(p \\/ q) -> p  is NOT valid" '((p bool) (q bool)) '(==> (or p q) p))
(refute! "~p  alone is NOT valid" '((p bool)) '(not p))
(refute! "excluded middle p \\/ ~p NOT intuitionistically provable (no axioms)"
         '((p bool)) '(or p (not p)))

(format t "~%=== ~a passed, ~a failed ===~%" *pass* *fail*)
(if (zerop *fail*) (sb-ext:exit :code 0) (sb-ext:exit :code 1))
