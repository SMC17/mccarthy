;;;; The autonomous prover must FIND and CERTIFY proofs of nontrivial theorems
;;;; from their s-expression statements alone.
(load (merge-pathnames "../src/load.lisp" *load-pathname*))
(in-package :mccarthy)

(defvar *pass* 0) (defvar *fail* 0)
(defun prove! (name sig goal &optional (depth 14))
  (multiple-value-bind (th g) (prove-sexp sig goal :depth depth)
    (cond ((and th (aconv (concl th) g) (null (hyp th)))
           (incf *pass*) (format t "  PROVED  ~a~%            ~a~%" name (pp (concl th))))
          (t (incf *fail*) (format t "  FAILED  ~a  (~a)~%" name goal)))))
(defun refute! (name sig goal &optional (depth 10))
  ;; the prover must NOT claim to prove a non-theorem
  (multiple-value-bind (th g) (prove-sexp sig goal :depth depth) (declare (ignore g))
    (cond (th (incf *fail*) (format t "  UNSOUND ~a  (proved a non-theorem!)~%" name))
          (t (incf *pass*) (format t "  rejected ~a  (correctly found no proof)~%" name)))))

(format t "~%=== autonomous prover ===~%")

;; propositional
(prove! "conjunction commutes" '((p bool) (q bool))
        '(==> (and p q) (and q p)))
(prove! "implication is reflexive" '((p bool)) '(==> p p))
(prove! "and-elim left" '((p bool) (q bool)) '(==> (and p q) p))
(prove! "currying chain  (p->q)->(q->r)->(p->r)" '((p bool) (q bool) (r bool))
        '(==> (==> p q) (==> (==> q r) (==> p r))))
(prove! "modus ponens packaged  p -> (p->q) -> q" '((p bool) (q bool))
        '(==> p (==> (==> p q) q)))
(prove! "conjunction of hypotheses  p -> q -> (p/\\q)" '((p bool) (q bool))
        '(==> p (==> q (and p q))))

;; quantifiers
(prove! "forall reflexivity  !x. x=x" '() '(! (x a) (= x x)))
(prove! "universal instantiation  (!x.P x) -> P c" '((p (fun a bool)) (c a))
        '(==> (! (x a) (p x)) (p c)))
(prove! "universal modus ponens  (!x.P x->Q x)->(!x.P x)->(!y.Q y)"
        '((p (fun a bool)) (q (fun a bool)))
        '(==> (! (x a) (==> (p x) (q x)))
              (==> (! (x a) (p x)) (! (y a) (q y)))))
(prove! "distribute forall over impl antecedent  (!x.P x) -> (!x. (P x /\\ P x))"
        '((p (fun a bool)))
        '(==> (! (x a) (p x)) (! (x a) (and (p x) (p x)))))

;; soundness: non-theorems must be rejected (no false proofs)
(refute! "p -> q  is NOT valid" '((p bool) (q bool)) '(==> p q))
(refute! "(p\\/?) bogus: p  alone" '((p bool)) '(p))
(refute! "exists-like  (P c) -> (!x. P x)  is NOT valid" '((p (fun a bool)) (c a))
         '(==> (p c) (! (x a) (p x))))

;; reflective self-extension: learn a lemma, reuse it
(format t "  -- reflective: learn a lemma and reuse it --~%")
(multiple-value-bind (lem g) (prove-sexp '((p bool) (q bool)) '(==> (and p q) (and q p)))
  (declare (ignore g))
  (learn lem)
  (format t "  learned: ~a   (*facts* now has ~a)~%" (pp (concl lem)) (length *facts*)))

(format t "~%=== ~a passed, ~a failed ===~%" *pass* *fail*)
(if (zerop *fail*) (sb-ext:exit :code 0) (sb-ext:exit :code 1))
