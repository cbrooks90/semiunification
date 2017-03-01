(define var vector)
(define var? vector?)
(define (var=? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

(define (redex SUP)
  (if (null? SUP) '()
      (let ([ineq (car SUP)])
        (cons (cond [(redex-I? ineq) (reduce-I ineq)]
                    [(redex-II? ineq) (reduce-II ineq)]
                    [else ineq])
              (redex (cdr SUP))))))
