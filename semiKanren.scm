;; Jason Hemann and Dan Friedman
;; from "μKanren: A Minimal Functional Core for Relational Programming",
;; with bonus semiunification by Chris Brooks

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (and (vector? x1) (equal? x1 x2)))

(define (state s b vc ec)
  `(,s ,b ,vc . ,ec))
(define subst car)
(define bounds cadr)
(define var-no caddr)
(define eq-no cdddr)

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
    (let-values (((s bounds) (semiunify u v (subst s/c) (bounds s/c))))
      (if s (unit (state s bounds (var-no s/c) (+ (eq-no s/c) 1)))
          mzero))))

(define (== u v)
  (lambda (s/c)
    (let-values (((_ s) (unify u v (subst s/c))))
      (if s (unit (state s (bounds s/c) (var-no s/c) (eq-no s/c))) mzero))))

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

;; Need to invert the anti-substitution and append it
(define (adjust-upper-bound v term s bounds)
  (let ((b (assoc v bounds)))
    (if b
        (let-values (((term anti-s _) (antiunify (cddr b) term s 'idk)))
          (cons (cons v (cons (cadr b) term)) bounds))
        (cons (cons v (cons 'bottom term)) bounds))))

;; Need to factor out common symbols from the endpoints and update the subsitution.
;; This also applies to the above
(define (adjust-lower-bound v term s bounds)
  (let ((b (assoc v bounds)))
    (if b
        (let-values (((term s) (unify (cadr b) term s 'idk)))
          (cons (cons v (cons term (cddr b))) bounds))
        (cons (cons v (cons term 'top)) bounds))))

(define (semiunify l r s bounds)
  (let ((l (walk l s))
        (r (walk r s)))
    (cond
     ((var? l) (values s (adjust-upper-bound l r s bounds)))
     ((var? r) (values s (adjust-lower-bound r l s bounds)))
     ((and (pair? u) (pair? v))
      (let*-values (((s bounds) (semiunify (car u) (car v) s bounds))
                    ((s bounds) (semiunify (cdr u) (cdr v) s bounds)))
        (values s bounds)))
     ((equal? u v) (values s bounds))
     (else #f))))

(define (call/fresh f)
  (lambda (s/c)
    (let ((c (var-no s/c)))
      ((f (var c)) (state (subst s/c) (bounds s/c) (+ c 1) (eq-no s/c))))))

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
