(load "match.scm")

(define var vector)
(define var? vector?)
(define (var=? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

(define (parse-term term env)
  (match term
    [,v
     (guard (symbol? v))
     (if (null? env) (values (var 0) (cons (cons v 0) env))
         (let ([binding (assq v env)])
           (if binding (values (var (cdr binding)) env)
               (let ([var-num (+ (cdar env) 1)])
                 (values (var var-num) (cons (cons v var-num) env))))))]
    [(,fn . ,args)
     (guard (symbol? fn))
     (let loop ([args args] [accum '()] [env env])
       (if (null? args) (values (cons fn (reverse accum)) env)
           (let-values ([(arg env) (parse-term (car args) env)])
             (loop (cdr args) (cons arg accum) env))))]
    [,x (error 'parse "Expected constructor or symbol, got ~s" x)]))

(define (parse-ineq ineq env)
  (match ineq
    [(< ,lhs ,rhs)
     (let*-values ([(lhs env) (parse-term lhs env)]
                   [(rhs env) (parse-term rhs env)])
       (values `(< ,lhs ,rhs) env))]
    [,x (error 'parse "Malformed inequality ~s" x)]))

(define (parse-list li env)
  (match li
    [() '()]
    [(,first . ,rest)
     (let-values ([(ineq env) (parse-ineq first env)])
       (cons ineq (parse-list rest env)))]
    [,x (error 'parse "Malformed list ~s" x)]))

(define (parse SUP)
  (parse-list SUP '()))
