; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env k)
    (apply-k k (extended-env-record syms (map-cps cell vals k) env))))

(define extend-env-recursively
  (lambda (proc-names idss bodies old-env k)
    (apply-k k (recursively-extended-env-record
      proc-names idss bodies old-env))))
	
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

(define cell
  (lambda (item k)
    (apply-k (box item))))


(define cell-ref
  (lambda (item)
    (unbox item)))

(define cell?
  (lambda (item)
    (box? item)))

(define set-cell!
  (lambda (item val)
    (set-box! item val)))

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
    (cases environment env
      (empty-env-record ()
        (fail))
      (extended-env-record (syms vals env)
	(let ((pos (list-find-position sym syms)))
      	  (if (number? pos)
	      (apply-k succeed (unbox (list-ref vals pos)))
	      (apply-env env sym succeed fail))))
      [recursively-extended-env-record (proc-names idss bodies old-env)
        (let ([pos (list-find-position sym proc-names)])
          (if (number? pos)
              (closure (list-ref idss pos) (list (list-ref bodies pos)) env)
              (apply-env old-env sym succeed fail)))])))

(define map-cps
  (lambda (proc ls k)
    (if (null? ls)
      (apply-k k '())
      (map-cps proc (cdr ls) (lambda (cdr-ls) (proc (car ls) (lambda(x) (apply-k k (cons x cdr-ls)))))))))

(define apply-k
  (lambda (k val)
    (cases continuation k
      [test-k (then-exp else-exp env k)
        (if val
            (eval-exp then-exp env k)
            (eval-exp else-exp env k))]
      [test-single-k (then-exp env k)
        (if val
            (eval-exp then-exp env k))]
      [rator-k (rands env k)
        (eval-rands rands env (rands-k val k))]
      [rands-k (proc-value k)
        (apply-proc proc-value val k)]
      [let-rands-k (syms env bodies k)
        (extend-env syms val env (let-extend-k bodies k))]
      [let-extend-k (bodies k)
        (eval-in-order bodies val k)]
      [letrec-extend-k (bodies k)
        (eval-in-order bodies val k)]
      [while-test-k (test-exp bodies env k)
        (if val
           (eval-in-order bodies env (continue-while-k test-exp bodies env k))
           #t)]
      [continue-while-k (test-exp bodies env k)
        (eval-while test-exp bodies env (while-test-k test-exp bodies env k))]
      [and-k (env k)
        (cond
          [(null? val) #t]
          [(null? (cdr val)) (eval-exp (car val) env k)]
          [else (eval-exp (car val) env (2-and-k val env k))])]
      [2-and-k (body env k)
       (if val
           (eval-or (cdr body) env (or-k env k))
           #f)]
      [or-k (env k)
        (cond
         	[(null? val) #f]
          [(null? (cdr val)) (eval-exp (car val) env k)]
          [else (eval-exp (car val) env (2-or-k val env k))])]
      [2-or-k (body env k)
       (if val
         val
         (eval-or (cdr body) env (or-k env k)))]
      [pos-set!-k (id body vals env eval-env k)
        (if (number? val)
            (eval-exp body eval-env (2-pos-set!-k val vals))
            (eval-set! id body env eval-env k))]
      [2-pos-set!-k (pos vals)
        (set-cell! (list-ref vals pos) val)]

      [order-eval-k (body env k) (eval-in-order body env k)]
      [id-k () ((lambda (v) v) val)]
      )))