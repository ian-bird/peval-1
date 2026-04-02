(use-modules (ice-9 match))

;; perform beta reduction on a lambda body.
;; if a lambda sub-expression could cause a collision,
;; do alpha-reduction on it before continuing down into it
;; to complete the beta-reduction
(define (lambda-reduce body param arg)
  (cond ((and (symbol? body) (eq? body param))
	 arg)
	((and (list? body)
	      (eq? (car body) 'lambda)
	      (or (eq? (cadr body) param)
		  (eq? (cadr body) arg)))
	 (let ((new-param (gensym)))		  
	   `(lambda ,new-param
	      ,(lambda-reduce (lambda-reduce (caddr body) (cadr body) new-param)
			      param
			      arg))))
	((list? body)
	 (map (lambda (v) (lambda-reduce v param arg)) body))
	(else body)))

;; evaluator for the unary, untyped, pure lambda calculus, extended to use
;; a global environment.
(define (neval expr env)
  (match expr
    ;; lambda is self-evaluating
    (('lambda param body) expr)
    ;; function application with known lambda is handled
    ;; by beta-reduction & alpha reduction when needed and then evaluation of the result
    ((('lambda param body) argument)
     (neval (lambda-reduce body param argument) env))
    ;; if the first argument of the application isn't a lambda,
    ;; evaluate it again and try again.
    ((unevaled-f argument)
     (neval `(,(neval unevaled-f env) ,argument) env))
    ;; otherwise, if it's a symbol, look up the binding,
    ;; and if it's not, error.
    (else (if (symbol? expr)
	      (let ((binding (assq expr env)))
		(if (pair? binding)
		    (cdr binding)
		    (error "unbound variable " expr)))
	      (error "failed to evaluate" expr)))))

;; we can think of partial evaluation as an extension of normal order evaluation with support
;; for unbound variables.
(define (peval expr env)
  (match expr
    ;; lambda no longer has to self evaluate. So update this to eval the body,
    ;; gracefully handling unbound variables.
    (('lambda param body) `(lambda ,param ,(peval body env)))
    ;; function application with known lambda is handled
    ;; by beta-reduction & alpha reduction when necessary and then evaluation of the result
    ((('lambda param body) argument)
     (peval (lambda-reduce body param argument) env))
    ;; if the first argument of the application isn't a lambda,
    ;; evaluate it again and try again, unless its unbound.
    ;; reduce until we reach a fixed point.
    ((unevaled-f argument)
     (call-with-values (lambda () (peval unevaled-f env))
       (lambda (result . unbound)	; <--- added this and line above to get the flag
	 (if (and (null? unbound) (not (equal? result unevaled-f))) ; <--- add test to see if first term is least fixed point
	     (peval `(,result ,argument) env)
	     `(,result ,(peval argument env))))))
    ;; otherwise, if it's a symbol, look up the binding,
    ;; and if it's not, error.
    (else (if (symbol? expr)
	      (let ((binding (assq expr env)))
		(if (pair? binding)
		    (cdr binding)
		    (values expr 'unbound))) ; <--- changed this to return an unbound flag
	      (error "failed to evaluate" expr)))))

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
;; peval \a.add(zero)(a) => \a.a
;;

(peval '(lambda a (car ((cons a) omega)))
       '((cons . (lambda a (lambda b (lambda s ((s a) b)))))
	 (car . (lambda c (c (lambda a (lambda b a)))))
	 (omega . ((lambda x (x x)) (lambda x (x x))))
	 (true . (lambda c (lambda a c)))
	 (false . (lambda c (lambda a a)))
	 (if . (lambda p (lambda c (lambda a ((p c) a)))))
	 (or . (lambda a (lambda b (((if a) true) b))))
	 (and . (lambda a (lambda b (((if a) b) false))))
	 (zero . (lambda f (lambda x x)))
	 (constantly . (lambda c (lambda x c)))
	 (zero? . (lambda n ((n (constantly false)) true)))
	 (succ . (lambda n (lambda f (lambda x (f ((n f) x))))))
	 (pred . (lambda n (lambda f (lambda x (((n (lambda g (lambda h ((h g) f)))) (lambda u x)) (lambda u u))))))
         (add . (lambda a (lambda b (((if (zero? a)) b) (succ ((add (pred a)) b))))))))
