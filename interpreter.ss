; top-level-eval evaluates a form in the global environment

(display "before anything")
(newline)

(define *prim-proc-names* '(+ - * add1 sub1 cons = / not zero? car cdr list null?
              assq eq? equal? atom? length list->vector list? pair?
              procedure? vector->list vector vector? number? symbol?
              caar cadr cadar >= <= > < make-vector vector-ref set-car! set-cdr! display newline
              map apply quotient vector-set! member list-tail append eqv? display newline))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)
     (id-k)))

(display "make init-env")
(newline)

(define make-init-env
  (lambda () init-env))
 
(define global-env init-env)

(define reset-global-env
 (lambda () (set! global-env (make-init-env))))

(display "reset global env")
(newline)

(define top-level-eval
  (lambda (form)
    (cases expression form
      [begin-exp (body) (if (equal? (caar body) 'define-exp)
                                (begin (set! global-env
                                         (extend-env (list (cadar body)) (list (eval-exp (caar (cddr (car body))) global-env)) global-env (id-k)))
                                  (top-level-eval (begin-exp (cdr body))))
                                (eval-exp form global-env (id-k)))]
      [define-exp (name val) (set! global-env (extend-env (list name) (list (eval-exp (car val) global-env)) global-env (id-k)))]
      [else (eval-exp form (empty-env) (id-k))])))

(display "eval-exp")
(newline)

(define eval-exp
  (lambda (exp env k)
    (cases expression exp	
      	[lit-exp (datum) (apply-k k datum)]

      	[var-exp (id) (apply-env env id k (lambda ()
                                                        (apply-env global-env
                                                          id
                                                          k
                                                          (lambda ()
                                                            (eopl:error 'apply-env
                                          		                  "variable not found in environment: ~s"
                                                       			   	id)))))]
      	[app-exp (rator rands)
        	(let* ([proc-value (eval-exp rator env (rator-k rands env k))]
             	[args (eval-rands rands env (rands-k proc-value k))])
          		(apply-proc proc-value args k))]

      	[if-exp (condition body)
         (eval-exp condition env (test-single-k body env k))]
      	[if-else-exp (condition body1 body2)
         (eval-exp condition env (test-k body1 body2 env k))]

        [let-exp (vars vals body)
          (eval-rands vals env (let-rands-k vars env body k))]
      
        [letrec-exp (proc-names vars bodies letrec-body)
          (extend-env-recursively proc-names vars bodies env
            (letrec-extend-k letrec-body k))]
      
        [lambda-exp (id body) 
          (closure id body env)]
			
        [lambda-dot-exp (id arbitrary-id body)
         	(dot-closure id arbitrary-id body env)]
			
        [lambda-arbitrary-exp (id body)
         	(arb-closure id body env)]

        [while-exp (test-exp bodies)
          (eval-while test-exp bodies env (while-test-k test-exp bodies env k))]
			
	[void-exp ()
  	  (void)]

	[and-exp (args)
          (eval-and args env (and-k env k))]
			
	[or-exp (body)
          (eval-or body env (or-k env k))]
                          
	[begin-exp (body) 
          (eval-in-order body env k)]
                          
        [set!-exp (id body) (eval-set! id body env env k)]
        
      	[else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))
	
(display "eval-set!")
(newline)

(define eval-set!
  (lambda (id body new-env eval-env k)
    (cases environment new-env
      [empty-env-record () (check-global id body global-env eval-env k)]
      [extended-env-record (syms vals env)
        (apply-k (pos-set!-k id body vals env eval-env k) (list-find-position id syms))]
      [recursively-extended-env-record (proc-names idss bodies old-env)
        (eval-set! id body old-env old-env k)])))

(display "check global")
(newline)

(define check-global
  (lambda (id body global eval-env k)
    (cases environment global
      [empty-env-record () (apply-k k '())]
      [extended-env-record (syms vals env)
        (apply-k (pos-set!-k id body vals env eval-env k) (list-find-position id syms))]
      [recursively-extended-env-record (proc-names idss bodies old-env)
        (apply-k k '())])))

(display "eval-while")
(newline)

(define eval-while
  (lambda (test-exp bodies env k)
    (eval-exp test-exp env k)))

(display "eval and")
(newline)

(define eval-and
  (lambda (body env k)
    (apply-k k body)))
    
(display "eval or")
(newline)

(define eval-or
  (lambda (body env k)
    (apply-k k body)))

(display "eval-in-order")
(newline)

(define eval-in-order
      (lambda (body env k)
            (cond
              [(null? (cdr body)) (eval-exp (car body) env k)]
              [else (eval-exp (car body) env (order-eval-k (cdr body) env k))])))
                          
(display "eval rands")
(newline)

(define eval-rands
  (lambda (rands env k)
    (map-cps (lambda (expr k) (eval-exp expr env k)) rands (id-k))))
                

(display "apply proc")
(newline)        

(define apply-proc
  (lambda (proc-value args k)
    (if (box? proc-value)
        (cases proc-val (unbox proc-value)
          [prim-proc (op) (apply-k k (apply-prim-proc op args))]
          [closure (vars bodies env) (eval-in-order bodies (extend-env vars args env (id-k)) k)]
       	  [dot-closure (vars dot-var bodies env)
          		(eval-in-order bodies (dot-extend-env vars dot-var args env) k)]
       	  [arb-closure (arb-var bodies env)
          		(eval-in-order bodies (extend-env (list arb-var) (list args) env (id-k)) k)]
          [else (error 'apply-proc
                  "Attempt to apply bad procedure: ~s" 
                  proc-value)])
        (cases proc-val proc-value
          [prim-proc (op) (apply-k k (apply-prim-proc op args))]
          [closure (vars bodies env) (eval-in-order bodies (extend-env vars args env (id-k)) k)]
       	  [dot-closure (vars dot-var bodies env)
          		(eval-in-order bodies (dot-extend-env vars dot-var args env) k)]
       	  [arb-closure (arb-var bodies env)
          		(eval-in-order bodies (extend-env (list arb-var) (list args k) env (id-k)) k)]
          [else (error 'apply-proc
                  "Attempt to apply bad procedure: ~s" 
                  proc-value)]))))

(define syntax-expand
	(lambda (exp)
		(cases expression exp
			[lit-exp (datum) exp]
			[var-exp (id) exp]
			[if-exp (condition body) (if-exp (syntax-expand condition) (syntax-expand body))]
			[if-else-exp (condition body1 body2) 
				  (if-else-exp (syntax-expand condition) (syntax-expand body1) (syntax-expand body2))]
			[lambda-exp (id body) (lambda-exp id (map syntax-expand body))]

                        [letrec-exp (proc-names vars bodies letrec-body)
                                (letrec-exp proc-names vars (map syntax-expand bodies) (map syntax-expand letrec-body))]
    
                        [let-exp (vars vals body)
				(app-exp (lambda-exp vars (map syntax-expand body)) (map syntax-expand vals))]
    
                        [named-let-exp (id vars vals body)
                                (let-exp vars vals (list (letrec-exp (list id) (list vars) (map syntax-expand body) (map syntax-expand body))))]
    
			[while-exp (test-exp bodies) (while-exp (syntax-expand test-exp) (map syntax-expand bodies))]
			[app-exp (rator rands) (app-exp (syntax-expand rator) (map syntax-expand rands))]

			[or-exp (body) (or-exp (map syntax-expand body))]
			
			[and-exp (body) (and-exp (map syntax-expand body))]

			[begin-exp (body) (begin-exp (map syntax-expand body))]

			[case-exp (key cases bodies) (expand-case-helper key cases bodies)]

      [cond-exp (conditions body)
           (let helper ([cases conditions] [dos body])
                      (cond
                        [(null? (cdr cases)) (if (eqv? (car cases) 'else)
                                                        (if-exp (syntax-expand (car cases)) (syntax-expand (car dos)))
                                                        (syntax-expand (car dos)))]
                        [else (if-else-exp (syntax-expand (car cases)) (syntax-expand (car dos)) (helper (cdr cases) (cdr dos)))]))]


                        [let*-exp (vars vals body) (expand-let* vars vals body)]
                        
        [define-exp (name val) (define-exp name (map syntax-expand val))] 

			[else exp]
			)))

(define expand-let*
     (lambda (vars vals body)
          (if (null? (cdr vars))
               (let-exp (list (car vars)) (list (syntax-expand (car vals))) (map syntax-expand body))
               (let-exp (list (car vars)) (list (syntax-expand (car vals))) (list (expand-let* (cdr vars) (cdr vals) body))))))

(define expand-case-helper
	(lambda (key cases bodies)
		(syntax-expand (case-helper2 key cases bodies))))

(define case-helper2
  (lambda (key cases bodies)
    (cond
        [(eqv? 'else (car cases)) (if-exp (lit-exp #t) (syntax-expand (car bodies)))]
        [else
          [if-else-exp (app-exp (var-exp 'member) (list (syntax-expand key) (app-exp (var-exp 'list)  (car cases))  ))
               (syntax-expand (car bodies)) (case-helper2 key (cdr cases) (cdr bodies))]]
   )))

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(add1) (+ (car args) 1)]
      [(sub1) (- (car args) 1)]
      [(cons) (cons (car args) (cadr args))]
      [(=) (= (car args) (cadr args))]
      [(/) (apply / args)]
      [(not) (not (car args))]
      [(zero?) (zero? (car args))]
      [(display) (display (car args))]
      [(newline) (newline)]

      [(car) (car (car args))]
      [(cdr) (cdr (car args))]
      [(list) args]
      [(list-tail) (list-tail (car args) (cadr args))]
      [(null?) (null? (car args))]
      [(assq) (assq (car args) (cadr args))]
      [(eq?) (eq? (car args) (cadr args))]
      [(equal?) (equal? (car args) (cadr args))]
      [(eqv?) (eqv? (car args) (cadr args))]
      [(atom?) (atom? (car args))]
      [(length) (length (car args))]
      [(list->vector) (list->vector (car args))]
      [(list?) (list? (car args))]
      [(pair?) (pair? (car args))]
      [(procedure?) (proc-val? (car args))]			
      [(vector->list) (vector->list (car args))]
      [(vector) (apply vector args)]
      [(vector?) (vector? (car args))]
      [(number?) (number? (car args))]
      [(symbol?) (symbol? (car args))]
      [(caar) (caar (car args))]
      [(cadr) (cadr (car args))]
      [(cadar) (cadar (car args))]
      [(>=) (>= (car args) (cadr args))]
      [(<=) (<= (car args) (cadr args))]
      [(>) (> (car args) (cadr args))]
      [(<) (< (car args) (cadr args))]
      [(quotient) (quotient (car args) (cadr args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(map) (map (lambda (x) (apply-proc (car args) (list x))) (cadr args))]
      [(apply) (apply-proc (car args) (cadr args))]
  	  [(make-vector) (make-vector (car args))]
  	  [(vector-ref) (vector-ref (car args) (cadr args))]
  	  [(set-car!) (set-car! (car args) (cadr args))]
  	  [(set-cdr!) (set-cdr! (car args) (cadr args))]
  	  [(display) (display args)]
  	  [(newline) (newline)]
      [(member) (member (car args) (cadr args))]
      [(append) (apply append args)]
	

      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-op)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))


(define check-ref
	(lambda (id)
		(ormap list? id)))





