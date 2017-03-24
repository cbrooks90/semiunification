(load "parse.scm")

(define (freshen x) x)

(define (redex-args l-args r-args visited)
  (cond
    [(and (null? l-args) (null? r-args)) (values #f visited)]
    [(or (null? l-args) (null? r-args)) (error #f "Arity mismatch")]
    [else
     (let-values ([(subst visited~) (redex-term (car l-args) (car r-args))])
       (if subst
           (values subst #f)
           (redex-args (cdr l-args) (cdr r-args))))]))

(define (redex-term l r visited)
  (cond
    [(and (var? r) (not (var? l))) (values `(subst ,r ,(freshen l)) #f)]
    [(and (pair? l) (pair? r) (equal? (car l) (car r)))
     (redex-args l r visited)]
    [(var? l)
     (let ([prev-visit (assp (lambda (x) (var=? x l)) visited)])
       (if prev-visit
           ?
           (values #f (cons `(,l . ,r) visited))))]
    [else (values #f visited)]))

(define (redex ineq)
  (match ineq
    [(< ,lhs ,rhs) (redex-term lhs rhs '())]))
