; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (map box vals) env)))

(define extend-env-recursively
  (lambda (proc-names idss bodies old-env)
    (recursively-extended-env-record
      proc-names idss bodies old-env)))
	
(define dot-extend-env
	(lambda (syms dot-var vals env)
		(extend-env (append syms (list dot-var)) (dot-env-helper (length syms) vals) env)
	))
	(define dot-env-helper
		(lambda (len vals)
			(if (zero? len)
				(list vals)
				(cons (car vals) (dot-env-helper (- len 1)(cdr vals)))
			)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (recur-deref (apply-env-ref env sym succeed fail))))


(define (recur-deref cell)
  (if (box? cell)
    (recur-deref (unbox cell))
    cell
    )
  )


(define (deref cell)
  (unbox cell)
  )

(define (ref-set! cell value)
  (set-box! cell value)
  )


(define apply-env-ref
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
      (empty-env-record ()
        (apply-env-ref init-env sym succeed fail))
      
      (fail-env ()
        (fail) )
      
      (extended-env-record (syms vals env)
	       (let ((pos (list-find-position sym syms)))
      	(if (number? pos)
	      (succeed  (list-ref vals pos))
	      (apply-env-ref env sym succeed fail))))


  [recursively-extended-env-record
    (procnames idss bodies old-env)
    (let ([pos
    (list-find-position sym procnames)])
    
    (if (number? pos)
      
      (box (closure (list-ref idss pos)
      (list-ref bodies pos) env) )


      
    (apply-env-ref old-env sym succeed fail)))]


      )))

