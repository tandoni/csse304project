
;; Parsed expression datatypes

(define-datatype expression expression?
  
    [lit-exp (id lit?)]
    [var-exp (id symbol?)]
    [app-exp (rator expression?)
           (rand (list-of expression?)) ]
	
    [if-exp (condition expression?)
          (body expression?)]
    [if-else-exp (condition expression?)
               (body1 expression?)
               (body2 expression?)]
   ; [lit-exp (id lit2?)]
    [lambda-exp
		(id (list-of symbol?))
		(body (list-of expression?))]
	[lambda-dot-exp
		(id (list-of symbol?))
		(arbitrary-id symbol?)
		(body (list-of expression?))]
	[lambda-arbitrary-exp
		(id symbol?)
		(body (list-of expression?))]
    [let-exp (vars (list-of symbol?)) (vals (list-of expression?))
           (body (list-of expression?)) ]
    [let*-exp (vars (list-of symbol?)) (vals (list-of expression?))
            (body (list-of expression?))]
    [letrec-exp (proc-names (list-of symbol?)) (vars (list-of (list-of symbol?))) (bodies (list-of expression?))
              (letrec-body (list-of expression?))]
    [named-let-exp (id symbol?)
                 (vars (list-of symbol?)) (vals (list-of expression?))
                 (body (list-of expression?))]
    [set!-exp  (id symbol?)
             (body expression?)]
    [define-exp (name symbol?) (val (list-of expression?))]

    [cond-exp
      (conditions (list-of expression?))
      (body (list-of expression?))]

    [or-exp (body (list-of expression?))]
    [and-exp (args (list-of expression?))]

    [while-exp
		(test-exp expression?)
		(bodies list?)]

    [begin-exp (body (list-of expression?))]

    [case-exp (key expression?) (cases (lambda (x) (map (lambda (y) (or ((list-of expression?) y) (eq? y 'else))) x)))
    												(bodies (list-of expression?))]

	[void-exp]			 
    [vec-exp (id vector?)])

(define lit? 
  (lambda (x)
      (or (number? x) (vector? x) (boolean? x) (symbol? x) (string? x) (pair? x) (null? x))))


	
; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc  (name symbol?)]
  [closure    (vars (list-of symbol?)) (body (list-of expression?)) (env environment?)]
  [dot-closure
		(vars (list-of symbol?))
		(dot-var symbol?)
		(bodies (list-of expression?))
		(env environment?)]
  [arb-closure
		(arb-var symbol?)
		(bodies (list-of expression?))
		(env environment?)]
)
	 
	 
	 
	
;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?))
  (recursively-extended-env-record
    (proc-names (list-of symbol?))
    (vars (list-of (list-of symbol?)))
    (bodies (list-of expression?))
    (env environment?)))



