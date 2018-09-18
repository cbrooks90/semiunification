;; Jason Hemann and Dan Friedman
;; from "μKanren: A Minimal Functional Core for Relational Programming",
;; with bonus semiunification by Chris Brooks

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (and (vector? x1) (equal? x1 x2)))

(define (state s bds vc ec)
  `(,s ,bds ,vc . ,ec))
(define subst car)
(define bds cadr)
(define var-no caddr)
(define eq-no cdddr)

(define (walk u s)
  (let ((pr (and (var? u) (assp (lambda (v) (var=? u v)) s))))
    (if pr (walk (cdr pr) s) u)))

(define (bounds v li)
  (let ((pr (assp (lambda (x) (var=? x v)) li)))
    (if pr
        (cdr pr)
        `(,(vector 'bottom (vector-ref v 0)) . #f))))

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
    (let-values (((s bds _) (semiunify u v (subst s/c) (bds s/c) '())))
      (if s (unit (state s bds (var-no s/c) (+ (eq-no s/c) 1)))
          mzero))))

(define (== u v)
  (lambda (s/c)
    (let-values (((_ s) (unify u v (subst s/c))))
      (if s (unit (state s (bds s/c) (var-no s/c) (eq-no s/c))) mzero))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (antiunify u v)
  (cond
   ((not u) v)
   ((not v) u)
   ((var? u) u)
   ((var? v) v)
   ((and (pair? u) (pair? v))
    (cons (antiunify (car u) (car v)) (antiunify (cdr u) (cdr v))))
   ((equal? u v) u)
   (else (vector 'bottom))))

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
     ((and (var? u) (var? v) (var=? u v)) (values u s))
     ((var? u) (values v (ext-s u v s)))
     ((var? v) (values u (ext-s v u s)))
     ((and (pair? u) (pair? v))
      (let*-values (((t1 s) (unify (car u) (car v) s))
                    ((t2 s) (if s (unify (cdr u) (cdr v) s) (values #f #f))))
        (if s (values (cons t1 t2) s) (values #f #f))))
     ((equal? u v) (values u s))
     (else (values #f #f)))))

(define (<=? l r s)
  (let ((l (walk l s)) (r (walk r s)))
    (cond
     ((var? l))
     ((var? r) #f)
     ((and (pair? l) (pair? r))
      (and (semiunify-kinda (car l) (car r) s)
           (semiunify-kinda (cdr l) (cdr r) s)))
     ((equal? l r))
     (else #f))))

(define (factorize lb ub bds s pairs)
  (cond
   ((and (pair? lb) (pair? ub))
    (let*-values (((t1 bds pairs) (factorize (car lb) (car ub) bds s pairs))
                  ((t2 bds pairs) (if bds (factorize (cdr lb) (cdr ub) bds s pairs)
                                      (values #f #f pairs))))
      (values (cons t1 t2) bds pairs)))
   ((equal? lb ub) (values lb bds pairs))
   ((assp (lambda (x) (equal? (cons lb ub) x)) pairs)
    => (lambda (x) (values (cdr x) bds pairs)))
   (else
    (if (<=? lb ub s)
        (let ((x (vector (gensym))))
          (values x (cons (cons x (cons lb ub)) bds)
                  (cons (cons (cons lb ub) x) pairs)))
        (values #f #f pairs)))))

(define (adjust lb ub s bds v vs)
  (if (or (var? lb) (not ub))
      (values s (cons (cons v (cons lb ub)) bds) vs)
      (let-values (((term bds _) (factorize lb ub bds s '())))
        (cond ((not bds) (values #f bds vs))
              ((var? term) (values s bds vs))
              (else (values (ext-s v term s) bds vs))))))

(define (adjust-upper-bound v term s bds vs)
  (let-values (((_ s) (if (assoc v vs) (unify term (cdr (assoc v vs)) s) (values #f s))))
    (let ((b (bounds v bds))
          (vs (cons (cons v term) vs)))
      (adjust (car b) (antiunify (cdr b) term) s bds v vs))))

(define (adjust-lower-bound v term s bds vs)
  (let ((b (bounds v bds)))
    (let-values (((term s) (unify (car b) term s)))
      (adjust term (cdr b) s bds v vs))))

(define (semiunify l r s bds vs)
  (let ((l (walk l s)) (r (walk r s)))
    (cond
     ((and (var? l) (var? r))
      (let-values (((s bds vs) (adjust-upper-bound l r s bds vs)))
        (adjust-lower-bound r l s bds vs)))
     ((var? l) (adjust-upper-bound l r s bds vs))
     ((var? r) (adjust-lower-bound r l s bds vs))
     ((and (pair? l) (pair? r))
      (let-values (((s bds vs) (semiunify (car l) (car r) s bds vs)))
        (if s (semiunify (cdr l) (cdr r) s bds vs)
            (values #f bds vs))))
     ((equal? l r) (values s bds vs))
     (else (values #f bds vs)))))

(define (call/fresh f)
  (lambda (s/c)
    (let ((c (var-no s/c)))
      ((f (var c)) (state (subst s/c) (bds s/c) (+ c 1) (eq-no s/c))))))

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
