(load "parse.scm")

(define (freshen x) x)

(define (redex-args l-args r-args visited)
  (if (or (null? l-args) (null? r-args)) (values #f visited)
      (let-values
        ([(subst visited~) (redex-term (car l-args) (car r-args) visited)])
        (if subst
            (values subst #f)
            (redex-args (cdr l-args) (cdr r-args) visited~)))))

(define (redex-term l r visited)
  (cond
    [(and (var? r) (not (var? l))); Redex I
     (values `(subst ,r ,(freshen l)) #f)]
    [(and (pair? l) (pair? r) (equal? (car l) (car r)))
     (redex-args l r visited)]
    [(var? l)
     (let ([prev-visit (assp (lambda (x) (var=? x l)) visited)])
       (if (and prev-visit (not (equal? (cdr prev-visit) r))); Redex II
           (unify (cdr prev-visit) r)
           (values #f (cons `(,l . ,r) visited))))]
    [else (values #f visited)]))

(define (redex ineq)
  (match ineq
    [(< ,lhs ,rhs) (redex-term lhs rhs '())]))

(define (semiunify u v s))
