;;;; Equational reasoning via the matcher + rewrite engine. These need genuine
;;;; rewriting (congruence, substitution of equals), not just forward chaining.
(load (merge-pathnames "../src/load.lisp" *load-pathname*))
(in-package :mccarthy)

(defvar *pass* 0) (defvar *fail* 0)
(defun prove! (name sig goal &optional (depth 16))
  (multiple-value-bind (th g) (prove-sexp sig goal :depth depth)
    (cond ((and th (aconv (concl th) g) (null (hyp th)))
           (incf *pass*) (format t "  PROVED  ~a~%            ~a~%" name (pp (concl th))))
          (t (incf *fail*) (format t "  FAILED  ~a~%" name)))))
(defun refute! (name sig goal &optional (depth 12))
  (multiple-value-bind (th g) (prove-sexp sig goal :depth depth) (declare (ignore g))
    (cond (th (incf *fail*) (format t "  UNSOUND ~a~%" name))
          (t (incf *pass*) (format t "  rejected ~a~%" name)))))

(format t "~%=== equational rewriting ===~%")

;; symmetry, transitivity of equality via rewriting
(prove! "symmetry  (a=b) -> (b=a)" '((a a) (b a)) '(==> (= a b) (= b a)))
(prove! "transitivity  (a=b)->(b=c)->(a=c)" '((a a) (b a) (c a))
        '(==> (= a b) (==> (= b c) (= a c))))

;; congruence: equals applied to a function
(prove! "f-congruence  (a=b) -> (f a = f b)" '((a a) (b a) (f (fun a a)))
        '(==> (= a b) (= (f a) (f b))))

;; substitution of equals into a predicate (Leibniz)
(prove! "Leibniz  (a=b) -> P a -> P b" '((a a) (b a) (p (fun a bool)))
        '(==> (= a b) (==> (p a) (p b))))

;; rewriting with a SYNTHESIZED (specialized) quantified equation:
;;   from  !x. f x = g x  derive  h (f c) = h (g c)
(prove! "rewrite under context  (!x. f x = g x) -> h(f c)=h(g c)"
        '((f (fun a a)) (g (fun a a)) (h (fun a a)) (c a))
        '(==> (! (x a) (= (f x) (g x))) (= (h (f c)) (h (g c)))))

;; nested: chain two rewrites
(prove! "two-step rewrite  (a=b)->(b=c)-> f a = f c" '((a a)(b a)(c a)(f (fun a a)))
        '(==> (= a b) (==> (= b c) (= (f a) (f c)))))

;; soundness: must NOT prove a non-equation
(refute! "(a=b) -> (a=c)  is NOT valid" '((a a)(b a)(c a)) '(==> (= a b) (= a c)))
(refute! "(P a) -> (P b)  without a=b is NOT valid" '((a a)(b a)(p (fun a bool)))
         '(==> (p a) (p b)))

(format t "~%=== ~a passed, ~a failed ===~%" *pass* *fail*)
(if (zerop *fail*) (sb-ext:exit :code 0) (sb-ext:exit :code 1))
