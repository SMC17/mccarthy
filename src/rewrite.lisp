;;;; src/rewrite.lisp — term matching + a rewriting engine (untrusted).
;;;;
;;;; Adds the machinery for equational / computational reasoning:
;;;;   * TERM-MATCH : first-order matching with type instantiation. Only the
;;;;     designated metavariables are flexible; every other variable (and every
;;;;     bound variable) is rigid, so a rule like  a = b  rewrites exactly the
;;;;     term  a,  while a quantified rule  !x. f x = g x  rewrites every  f _.
;;;;   * REWR-CONV : turn an equational theorem into a conversion.
;;;;   * BOUNDED-DEPTH-CONV : terminating rewriting to normal form.
;;;; Everything still bottoms out in the kernel: a rewrite produces a real
;;;; |- lhs = rhs theorem via INST_TYPE / INST on the rule.

(in-package :mccarthy)

(export '(term-match rewr-conv bounded-depth-conv strip-foralls no-match))

(define-condition no-match (error) ())

(defun type-match1 (pty tty tyb)
  "Extend type substitution TYB so that PTY[TYB] = TTY.  All tyvars flexible."
  (cond
    ((htvar-p pty)
     (let ((ex (assoc (htvar-name pty) tyb :test #'string=)))
       (cond ((null ex) (acons (htvar-name pty) tty tyb))
             ((type= (cdr ex) tty) tyb)
             (t (error 'no-match)))))
    ((and (htapp-p pty) (htapp-p tty)
          (string= (htapp-op pty) (htapp-op tty))
          (= (length (htapp-args pty)) (length (htapp-args tty))))
     (loop for a in (htapp-args pty) for b in (htapp-args tty)
           do (setf tyb (type-match1 a b tyb)))
     tyb)
    (t (error 'no-match))))

(defun term-match (metavars pat tm)
  "First-order match.  Returns (values term-bindings type-bindings):
   term-bindings is an alist (instantiated-metavar . term),
   type-bindings is an alist (tyvar-name . htype).  Signals NO-MATCH on failure."
  (let ((tb '()) (tyb '()))
    (labels
        ((tymatch (p tt) (setf tyb (type-match1 p tt tyb)))
         (bound-partner (v benv) (cdr (assoc v benv :test #'term=)))
         (tmatch (p tt benv)
           (cond
             ;; flexible metavar, not shadowed by an enclosing binder
             ((and (hvar-p p) (member p metavars :test #'term=) (not (assoc p benv :test #'term=)))
              (tymatch (hvar-ty p) (type-of tt))
              (let* ((pk (make-hvar (hvar-name p) (type-subst tyb (hvar-ty p))))
                     (ex (assoc pk tb :test #'term=)))
                (if ex (unless (aconv (cdr ex) tt) (error 'no-match))
                    (push (cons pk tt) tb))))
             ;; rigid variable: bound -> must equal its partner; free -> same name & type
             ((hvar-p p)
              (let ((partner (bound-partner p benv)))
                (if partner
                    (unless (and (hvar-p tt) (term= partner tt)) (error 'no-match))
                    (progn (unless (hvar-p tt) (error 'no-match))
                           (tymatch (hvar-ty p) (hvar-ty tt))
                           (unless (string= (hvar-name p) (hvar-name tt)) (error 'no-match))))))
             ((hconst-p p)
              (unless (and (hconst-p tt) (string= (hconst-name p) (hconst-name tt))) (error 'no-match))
              (tymatch (hconst-ty p) (hconst-ty tt)))
             ((hcomb-p p)
              (unless (hcomb-p tt) (error 'no-match))
              (tmatch (hcomb-rator p) (hcomb-rator tt) benv)
              (tmatch (hcomb-rand p) (hcomb-rand tt) benv))
             ((habs-p p)
              (unless (habs-p tt) (error 'no-match))
              (tymatch (hvar-ty (habs-bv p)) (hvar-ty (habs-bv tt)))
              (tmatch (habs-body p) (habs-body tt) (acons (habs-bv p) (habs-bv tt) benv)))
             (t (error 'no-match)))))
      (tmatch pat tm '())
      (values tb tyb))))

;;; strip outer universal quantifiers, returning their vars as metavariables
(defun strip-foralls (th)
  (if (is-forall (concl th))
      (mvb (x bod) (dest-forall (concl th)) (declare (ignore bod))
        (let* ((x2 (variant (free-vars-list (list (concl th))) x))
               (sp (spec x2 th)))
          (mvb (mvs base) (strip-foralls sp) (values (cons x2 mvs) base))))
      (values '() th)))

;;; turn an equational theorem  |- (!...) l = r  into a conversion
(defun rewr-conv (eqthm)
  (mvb (metavars base) (strip-foralls eqthm)
    (unless (is-eq (concl base)) (error "rewr-conv: not an equation"))
    (let ((lhs (nth-value 0 (dest-eq (concl base)))))
      (lambda (tm)
        (handler-case
            (mvb (tb tyb) (term-match metavars lhs tm)
              (inst-thm tb (inst-type-thm tyb base)))   ; |- tm = r[match]
          (no-match () (error 'conv-fail)))))))

;;; bounded bottom-up rewriting (terminating even for looping rule sets)
(defvar *rw-fuel*)
(defun bounded-depth-conv (c &optional (fuel 2000))
  (lambda (tm)
    (let ((*rw-fuel* fuel))
      (labels ((dc (tm)
                 (let* ((th1 (sub-conv #'dc tm))
                        (r (nth-value 1 (dest-eq (concl th1)))))
                   (if (<= *rw-fuel* 0) th1
                       (handler-case
                           (let* ((th2 (funcall c r)))
                             (decf *rw-fuel*)
                             (trans (trans th1 th2) (dc (nth-value 1 (dest-eq (concl th2))))))
                         (conv-fail () th1))))))
        (dc tm)))))
