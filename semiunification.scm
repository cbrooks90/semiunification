(define var vector)
(define var? vector?)
(define (var=? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

(define (flatten term path)
  (cond [(or (var? term) (and (pair? term) (null? (cdr term))))
         (list (cons term path))]
        [else
         (let loop ([args (cdr term)] [i 0])
           (if (null? args) '()
               (append (flatten (car args) (append path (list (cons (car term) i))))
                       (loop (cdr args) (+ i 1)))))]))

(define (paths SUP)
  (values (flatten (car SUP) '())
          (flatten (cdr SUP) '())))

(define (resolve-path flat-term path)
  (if (null? path)
      (if (null? (cdr flat-term))
          (caar flat-term)
          flat-term)
      (resolve-path
        (let loop ([term-paths flat-term] [first (car path)])
          (cond [(null? term-paths) '()]
                [(equal? first (cadar term-paths))
                 (cons (cons (caar term-paths) (cddar term-paths))
                       (loop (cdr term-paths) first))]
                [else (loop (cdr term-paths) first)]))
        (cdr path))))

(define (freshen x) x)

(define (redex-I lhs rhs)
  (cond [(null? rhs) #f]
        [(var? (caar rhs))
         (let ([p (resolve-path lhs (cdar rhs))])
           (if (var? p)
               (redex-I lhs (cdr rhs))
               (cons (caar rhs) (freshen lhs))))]
        [else (redex-I lhs (cdr rhs))]))

(define (redex-II lhs rhs)
  (let loop1 ([lhs lhs])
    (if (null? (cdr lhs)) #f
        (let loop2 ([rest (cdr lhs)])
          (if (null? rest) (loop1 (cdr lhs))
              (let ([t1 (caar lhs)]
                    [t2 (caar rest)])
                (if (and (var? t1) (var? t2) (var=? t1 t2))
                    (let ([p1 (resolve-path rhs (cdar lhs))]
                          [p2 (resolve-path rhs (cdar rest))])
                      (if (equal? p1 p2) (loop2 (cdr rest))
                          (or (unify p1 p2) (loop2 (cdr rest)))))
                    (loop2 (cdr rest)))))))))

(define (redex SUP)
  (if (null? SUP) '()
      (let ([ineq (car SUP)])
        (cons (cond [(redex-I? ineq) (reduce-I ineq)]
                    [(redex-II? ineq) (reduce-II ineq)]
                    [else ineq])
              (redex (cdr SUP))))))
