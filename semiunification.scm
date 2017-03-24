(load "parse.scm")

(define (freshen x) x)

(define (redex-I-args l-args r-args)
  (cond
    [(and (null? l-args) (null? r-args)) #f?]
    [(or (null? l-args) (null? r-args)) (error #f "Arity mismatch")]
    [else (or (redex-I-term (car l-args) (car r-args))
              (redex-I-args (cdr l-args) (cdr r-args)))]))

(define (redex-I-term l r)
  (cond
    [(and (var r) (not (var l))) `(subst ,r ,(freshen l))]
    [(and (pair? l) (pair? r) (equal? (car l) (car r)))
     (redex-I-args l r)]
    [else #f]))

(define (redex-I ineq)
  (match ineq
    [(< ,lhs ,rhs) (redex-I-term lhs rhs)]))
