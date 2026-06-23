;;;; load.lisp — load the whole system in dependency order (no ASDF/quicklisp).
(let ((here (or *load-pathname* *default-pathname-defaults*)))
  (dolist (f '("kernel" "logic" "rewrite" "prover"))
    (load (merge-pathnames (format nil "~a.lisp" f) here))))
