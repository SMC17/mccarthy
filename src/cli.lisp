;;;; src/cli.lisp — stateless REPL service + command-line entry.
;;;;
;;;; The service reads request s-expressions from a stream and writes certified
;;;; response s-expressions back — the homoiconic analogue of Harmonic's Lean
;;;; REPL service: submit a form, receive a kernel-checked result as DATA.
;;;;
;;;; Requests:
;;;;   (prove :sig ((p bool)(q bool)) :goal (==> (and p q) (and q p)) [:depth N])
;;;;   (learn :sig (...) :goal (...))      ; prove, then add to the fact base
;;;;   (facts)                             ; list learned lemmas
;;;;   (reset)                             ; clear the fact base
;;;;   (quit)

(in-package :mccarthy)

(defun %resp-theorem (th)
  (list :theorem :hyp (mapcar #'pp (hyp th)) :concl (pp (concl th))
        :certified-by :kernel))

(defun handle-request (form)
  (unless (consp form) (return-from handle-request (list :error :malformed form)))
  (let ((args (cdr form)))
    (case (%key (car form))
      (:prove
       (mvb (th g) (prove-sexp (getf args :sig) (getf args :goal)
                               :depth (or (getf args :depth) 14))
         (if th (%resp-theorem th) (list :no-proof :goal (pp g)))))
      (:learn
       (mvb (th g) (prove-sexp (getf args :sig) (getf args :goal)
                               :depth (or (getf args :depth) 14))
         (if th (progn (learn th) (list :learned (pp (concl th)) :fact-count (length *facts*)))
             (list :no-proof :goal (pp g)))))
      (:facts (list :facts (mapcar #'pp (facts))))
      (:reset (forget) (list :ok :reset))
      (:quit (list :bye))
      (t (list :error :unknown-request (car form))))))

(defun serve (&optional (in *standard-input*) (out *standard-output*))
  "Read request forms until EOF; emit one response form per request."
  (loop for form = (read in nil :eof)
        until (eq form :eof) do
          (let ((resp (handler-case (handle-request form)
                        (error (e) (list :error (princ-to-string e))))))
            (let ((*print-case* :downcase) (*print-readably* nil))
              (prin1 resp out) (terpri out) (finish-output out))
            (when (eq (%key (and (consp form) (car form))) :quit) (return)))))

;;; ---- a tiny built-in demo so `mccarthy demo` shows something immediately ----

(defparameter *demo-requests*
  '((prove :sig ((p bool) (q bool)) :goal (==> (and p q) (and q p)))
    (prove :sig ((p bool) (q bool) (r bool))
           :goal (==> (==> p q) (==> (==> q r) (==> p r))))
    (prove :sig ((p (fun a bool)) (q (fun a bool)))
           :goal (==> (! (x a) (==> (p x) (q x)))
                      (==> (! (x a) (p x)) (! (y a) (q y)))))
    (prove :sig ((p bool) (q bool)) :goal (==> p q))))  ; <- a non-theorem; must report :no-proof

(defun demo (&optional (out *standard-output*))
  (format out "~&McCarthy — the Aristotle of Lisp.  Certified by a ~a-primitive HOL kernel.~%~%"
          10)
  (dolist (req *demo-requests*)
    (format out "  request : ~(~a~)~%" req)
    (let ((*print-case* :downcase))
      (format out "  response: ~a~%~%" (handle-request req)))))

(defun main ()
  (let ((cmd (second sb-ext:*posix-argv*)))
    (cond ((null cmd) (serve))
          ((string-equal cmd "serve") (serve))
          ((string-equal cmd "demo") (demo))
          (t (format t "usage: mccarthy [serve|demo]   (serve reads requests from stdin)~%")))))
