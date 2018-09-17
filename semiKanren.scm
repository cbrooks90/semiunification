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

(define (antiunify-top u bds id)
  (cond
   ((pair? u)
    (let*-values (((t1 bds) (antiunify-top (car u) bds id))
                  ((t2 bds) (antiunify-top (cdr u) bds id)))
      (values (cons t1 t2) bds)))
   ((var? u)
    (let ((v (list->vector (append (vector->list u) (list id)))))
      (values v (cons (cons v `(,u . #f)) bds))))
   (else (values u old))))

(define (antiunify u v s id)
  (let rec ((u u) (v v) (a-s '()) (count 0))
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
        (values x (cons (cons (cons u v) x) a-s) (+ count 1)))))))

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

(define (factorize lb ub v bds s vs)
  (cond
   ((not lb) (values s (cons (cons v `(,lb . ,ub)) bds) vs))
   ((not ub)
    (let-values (((term bds) (antiunify-top lb bds 'idk)))
      (values (cons (cons v term) s) bds vs)))
   (else
    (let*-values (((term a-s _) (antiunify lb ub s 'idk)))
      (let loop ((li a-s) (bds bds))
        (if (null? li) (values (cons (cons v term) s) bds vs)
            ;; Should I use the data from these checks?
            (let-values (((s~ bds~ vs~)
                          (semiunify (caaar li) (cdaar li) s bds '())))
              (if (equal? s s~)
                  (loop (cdr li) (cons (cons (cdar li) (caar li)) bds))
                  (values #f bds vs)))))))))

(define (adjust-upper-bound v term s bds vs)
  (if (member v vs)
      (let-values (((_ s) (unify term (cddr (assoc v bds)) s)))
        (values s bds vs))
      (let ((b (if (assoc v bds) (cdr (assoc v bds)) `(#f . #f)))
            (vs (cons v vs)))
        (if (cdr b)
            ;; TODO: The anti-substitution needs to be used
            (let-values (((term anti-s _) (antiunify (cdr b) term s 'idk)))
              (factorize (car b) term v bds s vs))
            (factorize (car b) term v bds s vs)))))

(define (adjust-lower-bound v term s bds vs)
  (let ((b (if (assoc v bds) (cdr (assoc v bds)) `(#f . #f))))
    (if (car b)
        (let-values (((term s) (unify (car b) term s)))
          (factorize term (cdr b) v bds s vs))
        (factorize term (cdr b) v bds s vs))))

(define (semiunify l r s bds vs)
  (let ((l (walk l s)) (r (walk r s)))
    (cond
     ((and (var? l) (var? r))
      (let-values (((s bds vs) (adjust-upper-bound l r s bds vs)))
        (adjust-lower-bound r l s bds vs)))
     ((var? l) (adjust-upper-bound l r s bds vs))
     ((var? r) (adjust-lower-bound r l s bds vs))
     ((and (pair? l) (pair? r))
      (let*-values (((s bds vs) (semiunify (car l) (car r) s bds vs))
                    ((s bds vs) (if s (semiunify (cdr l) (cdr r) s bds vs)
                                    (values #f bds vs))))
        (values s bds vs)))
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
