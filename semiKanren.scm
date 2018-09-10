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

(define (antiunify-top u old id)
  (cond
   ((pair? u)
    (let*-values (((t1 old) (antiunify-top (car u) id))
                  ((t2 old) (antiunify-top (cdr u) id)))
      (values (cons t1 t2) old)))
   ((var? u)
    (let ((v (list->vector (append (vector->list u) (list id)))))
      (values v (cons (cons v u) old))))
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

(define (factorize lb ub v lbs ubs s)
  (define (split anti-subst)
    (let loop ((li anti-subst) (lbs lbs) (ubs ubs))
      (if (null? li) (values lbs ubs)
          (loop (cdr li)
                (cons (cons (cdar li) (caaar li)) lbs)
                (cons (cons (cdar li) (cdaar li)) ubs)))))
  (cond
   ((not lb)
    (values s lbs (cons ub ubs)))
   ((not ub)
    (let-values (((term new-lbs) (antiunify-top (cdr lb) '() 'idk)))
      (values (cons (cons v term) s) (append new-lbs lbs) ubs)))
   ((and (var? (cdr ub)) (not (var? (cdr lb))))
    (values #f lbs ubs))
   (else
    (let-values (((term a-s _) (antiunify (cdr lb) (cdr ub) s 'idk)))
      (if (var? term) (values s (cons lb lbs) (cons ub ubs))
          (let-values (((new-lbs new-ubs) (split a-s)))
            (values (cons (cons v term) s) (append new-lbs lbs) (append new-ubs ubs))))))))

(define (adjust-upper-bound v term s lbs ubs)
  (let ((lb (assoc v lbs))
        (ub (assoc v ubs)))
    (if ub
        ;; TODO: The anti-substitution needs to be used
        (let-values (((term anti-s _) (antiunify (cdr ub) term s 'idk)))
          (factorize lb (cons v term) v lbs ubs s))
        (factorize lb (cons v term) v lbs ubs s))))

(define (adjust-lower-bound v term s lbs ubs)
  (let ((lb (assoc v lbs))
        (ub (assoc v ubs)))
    (if lb
        (let-values (((term s) (unify (cdr lb) term s)))
          (factorize (cons v term) ub v lbs ubs s))
        (factorize (cons v term) ub v lbs ubs s))))

(define (semiunify l r s lbs ubs)
  (let ((l (walk l s))
        (r (walk r s)))
    (cond
     ((var? l) (adjust-upper-bound l r s lbs ubs))
     ((var? r) (adjust-lower-bound r l s lbs ubs))
     ((and (pair? l) (pair? r))
      (let*-values (((s lbs ubs) (semiunify (car l) (car r) s lbs ubs))
                    ((s lbs ubs) (if s (semiunify (cdr l) (cdr r) s lbs ubs)
                                     (values #f lbs ubs))))
        (if s (values s lbs ubs) (values #f lbs ubs))))
     ((equal? l r) (values s lbs ubs))
     (else (values #f lbs ubs)))))

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
