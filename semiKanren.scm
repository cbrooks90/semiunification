;; Jason Hemann and Dan Friedman
;; from "μKanren: A Minimal Functional Core for Relational Programming",
;; with bonus semiunification by Chris Brooks

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (and (vector? x1) (equal? x1 x2)))
(define (var-instance? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

(define (state s vc ec)
  `(,s ,vc . ,ec))
(define subst car)
(define var-no cadr)
(define eq-no cddr)

(define (walk t s prev-known eqn)
  (let ((known (and (var? t) (assp (lambda (v) (var=? t v)) s)))
        (temp  (and (var? t) (assp (lambda (v) (var=? (specify t eqn) v)) s))))
    (cond
      (known (walk (cdr known) s (cdr known) eqn))
      (temp  (walk (cdr temp) s prev-known eqn))
      (else (values (or prev-known t) t)))))

(define (ext-s x v s)
  (define (occurs x v s)
    (cond
      ((var? v) (var-instance? v x))
      (else (and (pair? v) (or (occurs x (car v) s)
                               (occurs x (cdr v) s))))))
  (if (occurs x v s) #f `((,x . ,v) . ,s)))

(define (<= u v)
  (lambda (s/c)
    (let ((s (semiunify u v (subst s/c) (eq-no s/c))))
      (if s (unit (state s (var-no s/c) (+ (eq-no s/c) 1))) mzero))))

(define (== u v)
  (lambda (s/c)
    (let ((s (unify u v (subst s/c))))
      (if s (unit (state s (var-no s/c) (eq-no s/c))) mzero))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (specify t eqn)
  (define (aux-var v)
    (list->vector (append (vector->list v) (list eqn))))
  (cond ((var? t) (aux-var t))
        ((pair? t) (cons (specify (car t) eqn) (specify (cdr t) eqn)))
        (else t)))

(define (semiunify l r s eqn)
  (let-values (((_1 l) (walk l s #f eqn)) ((_2 r) (walk r s #f eqn)))
    (cond
      ((and (var? l) (var? r) (var=? l r)) s)
      ((and (var? l) (var? r)) (ext-s l r s))
      ((var? l) (ext-s (specify l eqn) r s))
      ((var? r) (ext-s r (specify l eqn) s))
      ((and (pair? l) (pair? r))
       (let ((s (semiunify (car l) (car r) s eqn)))
         (and s (semiunify (cdr l) (cdr r) s eqn))))
      (else (and (equal? l r) s)))))

(define (unify u v s)
  (let-values (((_1 u) (walk u s #f #f)) ((_2 v) (walk v s #f #f)))
    (cond
      ((and (var? u) (var? v) (var=? u v)) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s (unify (cdr u) (cdr v) s))))
      (else (and (equal? u v) s)))))

(define (call/fresh f)
  (lambda (s/c)
    (let ((c (var-no s/c)))
      ((f (var c)) (state (subst s/c) (+ c 1) (eq-no s/c))))))

(define (disj g1 g2) (lambda (s/c) (mplus (g1 s/c) (g2 s/c))))
(define (conj g1 g2) (lambda (s/c) (bind (g1 s/c) g2)))

(define (mplus $1 $2)
  (cond
    ((null? $1) $2)
    ((procedure? $1) (lambda () (mplus $2 ($1))))
    (else (cons (car $1) (mplus (cdr $1) $2)))))

(define (bind $ g)
  (cond
    ((null? $) mzero)
    ((procedure? $) (lambda () (bind ($) g)))
    (else (mplus (g (car $)) (bind (cdr $) g)))))
