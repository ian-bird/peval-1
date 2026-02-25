;;; this implemented a combined step for alpha and beta reduction.
;;; it steps through a lambda expression looking for instances of the parameter
;;; being worked on and replacing it with the given argument.
;;; alpha reduction is done by providing a gensym as the argument to rename it.
(define (combined-reduction expr param arg)
  ;; if we get a lambda, we need to do alpha reduction before we can
  ;; do beta reduction on the body.
  (cond ((and (list? expr)  (eq? 'lambda (car expr)))
	 (let ((new-sym (gensym)))
	   `(lambda
		,new-sym
	      ,(combined-reduction (combined-reduction (caddr expr)
						       (cadr expr)
						       new-sym)
				   param
				   arg))))
	;; if its an application then try to reduce both
	((list? expr)
	 (map (lambda (sub-expr)
		(combined-reduction sub-expr param arg))
	      expr))
	;; if its a symbol then replace it if its equal to the param
	((eq? expr param) arg)
	(else expr)))

;;; this checks if a variable in the environment is an unbound variable.
;;; this is critical since when we're performing partial evaluation many
;;; variables remain unbound.
(define (unbound? v) (and (pair? v) (eq? (car v) 'unbound)))

;;; do one partial evaluation step. The form yielded may not be optimal,
;;; so this may need to be applied again. I don't know if this can result
;;; in a cycle.
;;;
;;; the basic idea is as follows:
;;; 1) bindings in env can be expanded ahead of time to their lambda expressions.
;;;    (it should be noted that named variables is an extension of the pure lambda calculus,
;;;     but it makes testing easier)
;;;
;;; 2) application of lambda expressions can be beta-reduced as long as the function
;;;    isn't an unbound variable.
;;;
;;; 3) we can apply these rules inside the body of an unapplied lambda,
;;;    as long as we remember it's parameter is unbound.
(define (peval-step expr env)
  (let ((lambda? (lambda (x) (and (list? x) (eq? 'lambda (car x)) (= (length x) 3)))))
    ;; if we get a symbol then look it up and return the binding
    (cond ((symbol? expr) (cdr (assq expr env)))
	  ((number? expr) expr)
	  ;; if its a lambda expression, then peval the body,
	  ;; and then if it's unbound just return the var name,
	  ;; otherwise return the pevaled body.
	  ((lambda? expr)
           (let ((body (peval-step (caddr expr)
				   (acons (cadr expr)
					  (cons 'unbound (cadr expr))
					  env))))
	     `(lambda ,(cadr expr) ,(if (unbound? body) (cdr body) body))))
	  ;; if its an application, then peval the lambda.
	  ;; if its unbound, then put the var name in the function call slot,
	  ;; and peval the argument. Just return that, since we can't do more.
          ((list? expr)
           (let ((lambda-expr (peval-step (car expr) env)))
	     (if (unbound? lambda-expr)
		 (list (cdr lambda-expr)
		       (peval-step (cadr expr) env))
		 ;; if it's not unbound, then we can do a beta reduction if its a lambda,
		 ;; by replacing the application with the lambda body that has had its
		 ;; parameter replaced with the argument.
		 (if (lambda? lambda-expr)
		     (combined-reduction (caddr lambda-expr)
					 (cadr lambda-expr)
					 (cadr expr))
		     (list lambda-expr
			   (peval-step (cadr expr) env))))))
	  ((and (pair? expr) (eq? 'unbound (car expr)))
	   (cdr expr)))))

;; repeatedly perform reduction steps to a form until we reach one we've seen before.
(define (peval expr env)
  (let loop ((expr expr)
	     (seen (list expr)))
    (let ((next-step (peval-step expr env)))
      (if (member next-step seen)
	  next-step
	  (loop next-step (cons expr seen))))))

;; examples:
;; let car = \c.c(\a.\b.a)
;; let cons = \a.\b.\s.s(a)(b)
;; let omega = (\x.x(x))(\x.x(x))
;;
;; peval \a.\b.car(cons(a)(b)) => \a.\b.a
;; peval \a.\b.car(cons(a)(omega)) => \a.\b.a
;;
;; let identity = \x.x
;;
;; peval \a.identity(a) => \a.a
;;
