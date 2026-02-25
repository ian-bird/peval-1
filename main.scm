(define (eval. form env)
  (cond ((number? form) form)
	((boolean? form) form)
	((char? form) form)
	((string? form) form)
	((symbol? form) (lookup form env))
	((pair? form)
	 (let ((check-arity (lambda (n or-more?)
			      (unless ((if or-more? <= =) n (length (cdr form)))
				(error `("bad arity in " ,form ": got" ,(length (cdr form))
					 expected ,n ,@(if or-more? '("or more") '())))))))
	   (case (car form)
	     ((quote) (check-arity 1 #f)
	      (cadr form))
	     ((car) (check-arity 1 #f)
	      (car (eval. (cadr form) env)))
	     ((cdr) (check-arity 1 #f)
	      (cdr (eval. (cadr form) env)))
	     ((cons) (check-arity 2 #f)
	      (cons (eval. (cadr form) env) (eval. (caddr form) env)))
	     ((eq?) (apply eq? (evlis (cdr form) env)))
	     ((atom?) (check-arity 1 #f)
	      (not (pair? (eval. (cadr form) env))))
	     ((lambda) (check-arity 2 #f)
	      (list (cons 'env env)
		    (cons 'args (cadr form))
		    (cons 'body (caddr form))))
	     ((if) (check-arity 3 #f)
	      (if (eval. (cadr form) env)
		  (eval. (caddr form) env)
		  (eval. (cadddr form) env)))
	     (else
	      (let ((fn (eval. (car form) env)))
		(unless (or (procedure? fn)
			    (every? (lambda (k) (assoc k fn)) '(env args body)))
		  (error `(wrong type to apply: ,(car form))))
		(apply. fn
		 (evlis (cdr form) env)))))))
	(else (error 'invalid-type form))))



;; we can do constant folding
;; and inlining.
;; inlining will be limited to 10 levels.
;; we cannot tell if we wil be able to inline
;; in the general case (see collatz conjecture)
;; so we'll just give up if things go beyond 10 levels.
;;
;; as long as code stays purely functional inlining is always safe.
(define (peval form env depth)
  ;; if a binding isnt found in the env than instead of erroring we'll leave it unbound
  (cond ((number? form) form)
	((boolean? form) form)
	((char? form) form)
	((string? form) form)
	((symbol? form)
	 (with-exception-handler
	     (lambda _ form)
	   (lambda () (lookup form env))))
	((pair? form)
	 (case (car form)
	   ((quote) form)
	   ((car)
	    (let ((arg-peval (peval (cadr form) env (1+ depth))))
	      (if (eq? 'quote (car arg-peval))
		  (car ))))))))

(any? (lambda (pred) (pred x)) '(boolean? number? string? char?))

(define (any? pred seq)
  (if (eq? '() seq)
      #f
      (if (pred (car seq))
	  #t
	  (any? pred (cdr seq)))))

(if (boolean? x) 
       #t
       (if (number? x)
	   #t
	   (if (string? x)
	       #t
	       #f)))


(define (every? proc seq)
  (call/cc (lambda (done)
	     (for-each (lambda (v)
			 (unless (proc v)
			   (done #f)))
		       seq)
	     #t)))

(define (evlis forms env)
  (map (lambda (form) (eval. form env)) forms))

(define (last list)
  (if (null? (cdr list))
      (car list)
      (last (cdr list))))

(define (bind params args)
  (cond ((symbol? params) (list (cons params args)))
	((and (null? params) (null? args)) '())
	((null? params) (error `(got ,(length args) extra arguments)))
	((null? args) (error `(expected ,(length params) extra arguments)))
	(else (acons (car params) (car args) (bind (cdr params) (cdr args))))))

(define (apply. proc args)
  (if (procedure? proc)
      (apply proc args)
      (eval. (cdr (assoc 'body proc))
	     (cons (bind (cdr (assoc 'args proc)) args)
		   (cdr (assoc 'env proc))))))

(define (lookup v env)
  (call/cc (lambda (done)
	     (for-each (lambda (frame)
			 (when (assoc v frame)
			   (done (cdr (assoc v frame)))))
		       env)
	     (eval v (interaction-environment)))))

