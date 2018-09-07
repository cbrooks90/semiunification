;; Jason Hemann and Dan Friedman
;; from "μKanren: A Minimal Functional Core for Relational Programming",
;; with bonus semiunification by Chris Brooks

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (and (vector? x1) (equal? x1 x2)))

(define (state s lbs ubs vc ec)
  `(,s ,lbs ,ubs ,vc . ,ec))
(define subst car)
(define lbs cadr)
(define ubs caddr)
(define var-no cadddr)
(define eq-no cddddr)

(define (walk u s)
  (let ((pr (and (var? u) (assp (lambda (v) (var=? u v)) s))))
    (if pr (walk (cdr pr) s) u)))

(define (occurs x v s)
  (let ((v (walk v s)))
    (cond
     ((and (var? v) (eq? v x)))
     (else (and (pair? v) (or (occurs x (car v) s)
                              (occurs x (cdr v) s)))))))

(define (ext-s x v s)
  (cond
   #;((occurs x v s))
   (else (cons `(,x . ,v) s))))

(define (<= u v)
  (lambda (s/c)
    (let-values (((s lbs ubs) (semiunify u v (subst s/c) (lbs s/c) (ubs s/c))))
      (if s (unit (state s lbs ubs (var-no s/c) (+ (eq-no s/c) 1)))
          mzero))))

(define (== u v)
  (lambda (s/c)
    (let-values (((_ s) (unify u v (subst s/c))))
      (if s (unit (state s (lbs s/c) (ubs s/c) (var-no s/c) (eq-no s/c))) mzero))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (antiunify u v s id)
  (let rec ((u u) (v v) (a-s '()) (count 0))
    (let ((u (walk u s)) (v (walk v s)))
      (cond
       ((and (pair? u) (pair? v))
        (let*-values (((t1 a-s count) (rec (car u) (car v) a-s count))
                      ((t2 a-s count) (rec (cdr u) (cdr v) a-s count)))
          (values (cons t1 t2) a-s count)))
       ((equal? u v) (values u a-s count))
       ((assp (lambda (x) (equal? (cons u v) x)) a-s)
        => (lambda (x) (values (cdr x) a-s count)))
       (else
        (let ((x (vector id count)))
          (values x (cons (cons (cons u v) x) a-s) (+ count 1))))))))

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
     ((and (var? u) (var? v) (var=? u v)) (values u s))
     ((var? u) (values v (ext-s u v s)))
     ((var? v) (values u (ext-s v u s)))
     ((and (pair? u) (pair? v))
      (let*-values (((t1 s) (unify (car u) (car v) s))
                    ((t2 s) (unify (cdr u) (cdr v) s)))
        (values (cons t1 t2) s)))
     ((equal? u v) (values u s))
     (else (values #f s)))))

(define (factorize lb ub v lbs ubs s)
  (define (split anti-subst)
    #;todo
    (values '() '()))
  (let-values (((term a-s _) (antiunify lb ub s 'idk)))
    (if (var? term) (values s (cons (cons v lb) lbs) (cons (cons v ub) ubs))
        (let-values (((new-lbs new-ubs) (split a-s)))
          (values (cons (cons v term) s) (append new-lbs lbs) (append new-ubs ubs))))))

;; Need to invert the anti-substitution and append it
(define (adjust-upper-bound v term s lbs ubs)
  (let ((lb (assoc v lbs))
        (ub (assoc v ubs)))
    (if ub
        (let-values (((term anti-s _) (antiunify (cdr ub) term s 'idk)))
          (if lb
              (factorize (cdr lb) term v lbs ubs s)
              (values s lbs (cons (cons v term) ubs))))
        (values s lbs (cons (cons v term) ubs)))))

(define (adjust-lower-bound v term s lbs ubs)
  (let ((lb (assoc v lbs))
        (ub (assoc v ubs)))
    (if lb
        (let-values (((term s) (unify (cdr lb) term s 'idk)))
          (if ub
              (factorize term (cdr ub) v lbs ubs s)
              (values s (cons (cons v term) lbs) ubs)))
        (values s (cons (cons v term) lbs) ubs))))

(define (semiunify l r s lbs ubs)
  (let ((l (walk l s))
        (r (walk r s)))
    (cond
     ((var? l) (adjust-upper-bound l r s lbs ubs))
     ((var? r) (adjust-lower-bound r l s lbs ubs))
     ((and (pair? u) (pair? v))
      (let*-values (((s lbs ubs) (semiunify (car u) (car v) s lbs ubs))
                    ((s lbs ubs) (semiunify (cdr u) (cdr v) s lbs ubs)))
        (values s lbs ubs)))
     ((equal? u v) (values s lbs ubs))
     (else #f))))

(define (call/fresh f)
  (lambda (s/c)
    (let ((c (var-no s/c)))
      ((f (var c)) (state (subst s/c) (lbs s/c) (ubs s/c) (+ c 1) (eq-no s/c))))))

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
