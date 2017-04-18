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

(define (resolve-var v s)
  (let loop ((s s) (local #f))
    (cond [(null? s) local]
          [(and (var-instance? v (caar s)) (= (length (caar s)) 1))
           (cdar s)]
          [(equal? v (caar s)) (loop (cdr s) (cdar s))])))

(define (specify t eqn)
  (if (not eqn) t
      (let loop ((t t))
        (cond ((var? t) (list->vector (append (vector->list t) (list eqn))))
              ((pair? t) (cons (loop (car t)) (loop (cdr t))))
              (else t)))))

(define (walk u s eqn)
  (if (not (var? u)) u
      (cond
        ((resolve-var (specify u eqn) s) => (lambda (x) (walk x s eqn)))
        (else u))))

(define (occurs x v s)
  (let ((v (walk v s #f)))
    (cond ((and (var? v) (eq? v x)))
          ((and (var? v) (var-instance? v x)) (error #f "R-acyclicity violation"))
          (else (and (pair? v) (or (occurs x (car v) s)
                                   (occurs x (cdr v) s)))))))

(define (ext-s x v s)
  (if (occurs x v s) #f `((,x . ,v) . ,s)))

(define (<= u v)
  (lambda (s/c)
    (let ((s (semiunify u v (subst s/c) (eq-no s/c))))
      (if s (unit (state s (var-no s/c) (+ (eq-no s/c) 1))) mzero))))

(define (== u v)
  (lambda (s/c)
    (let ((s (semiunify u v (subst s/c) #f)))
      (if s (unit (state s (var-no s/c) (eq-no s/c))) mzero))))

(define (au u v)
  (lambda (s/c)
    (let ((s (antiunify u v (subst s/c))))
      (unit (state s (var-no s/c) (eq-no s/c))))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (antiunify u v s)
  (let ((u (walk u s #f)) (v (walk v s #f)))
    (cond
      ((and (pair? u) (pair? v))
       (let ((s (antiunify (car u) (car v) s)))
         (antiunify (cdr u) (cdr v) s)))
      ((equal? u v) s)
      ((var? u) (ext-s v u s))
      ((var? v) (ext-s u v s))
      (else
        (let ((x (fresh-var)))
          (ext-s x u (ext-s x v s)))))))

(define (semiunify l r s eqn)
  (let ((l (walk l s eqn)) (r (walk r s eqn)))
    (cond
      ((and (var? l) (var? r) (var=? l r)) s)
      ((var? l) (ext-s (specify l eqn) r s))
      ((var? r) (ext-s r (specify l eqn) s))
      ((and (pair? l) (pair? r))
       (let ((s (semiunify (car l) (car r) s eqn)))
         (and s (semiunify (cdr l) (cdr r) s eqn))))
      ((equal? l r) s)
      (else #f))))

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
