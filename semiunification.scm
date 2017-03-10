(load "parse.scm")
(load "examples.scm")

(define (arity-0? term)
  (and (list? term) (= (length term) 1) (atom? (car term))))

(define (flatten term path)
  (cond [(or (var? term) (arity-0? term))
         (list (cons term path))]
        [else
         (let loop ([args (cdr term)] [i 0])
           (if (null? args) '()
               (append (flatten (car args) (append path (list (cons (car term) i))))
                       (loop (cdr args) (+ i 1)))))]))

(define (path-sort ps)
  (sort
    (lambda (x y)
      (< (vector-ref (car x) 0)
         (vector-ref (car y) 0)))
    ps))

(define (paths ineq)
  (match ineq
    [(< ,lhs ,rhs)
     `(< ,(path-sort (flatten lhs '()))
         ,(path-sort (flatten rhs '())))]))

(define (explode SUP)
  (match SUP
    [() '()]
    [(,ineq . ,ineqs)
     (cons (paths ineq) (explode ineqs))]))

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

(define (redex-II-2 ineq)
  (match ineq
    [(< ,lhs ,rhs)
      (match lhs
        [(,a) #f]
        [((,a . ,p1) (,a . ,p2) . ,tail) (cons p1 p2)]
        [,_ (redex-II-2 `(< ,(cdr lhs) ,rhs))])]))
