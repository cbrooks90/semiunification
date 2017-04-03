;; Jason Hemann and Dan Friedman
;; from "μKanren: A Minimal Functional Core for Relational Programming",
;; with bonus semiunification by Chris Brooks

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (and (vector? x1) (equal? x1 x2)))
(define (var-instance? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

(define (state s semi-s vc ec)
  `(,s ,semi-s ,vc . ,ec))
(define subst car)
(define ssubst cadr
(define var-no caddr)
(define eq-no cdddr)

(define (walk u s s~)
  (let ((pr (and (var? u)
                 (or (assp (lambda (v) (var=? u v)) s)
                     (assp (lambda (v) (var=? u v)) s~)))))
    (if pr (walk (cdr pr) s) u)))

(define (occurs x v s s~)
  (let ((v (walk v s s~)))
    (cond
      ((var? v) (var-instance? v x))
      (else (and (pair? v) (or (occurs x (car v) s s~)
                               (occurs x (cdr v) s s~)))))))

(define (ext-s x v s)
  (if (occurs x v s) #f `((,x . ,v) . ,s)))

(define (<= u v)
  (lambda (s/c)
    (let-values (((s s~ _) (semiunify u v (subst s/c) (ssubst s/c) (eq-no s/c) '())))
      (if s (unit (state s s~ (var-no s/c) (+ (eq-no s/c) 1))) mzero))))

(define (== u v)
  (lambda (s/c)
    (let ((s (unify u v (subst s/c) (ssubst s/c))))
      (if s (unit (state s (ssubst s/c) (var-no s/c) (eq-no s/c))) mzero))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (freshen t eqn)
  (define (aux-var v)
    (list->vector (append (vector->list v) (list eqn))))
  (cond ((var? t) (aux-var t))
        ((pair? t) (cons (freshen (car t) eqn) (freshen (cdr t) eqn)))
        (else t)))

(define (semiunify l r s s~ eqn visited)
  (let ((l (walk l s s~)) (r (walk r s s~)))
    (cond
      ((var? l)
       (values s (ext-s l r s~) visited))
      ((var? r)
       (values (unify r (freshen l eqn) s s~) visited))
      ((and (pair? l) (pair? r))
       (let-values (((s visited) (semiunify (car l) (car r) s s~ eqn visited)))
         (if s
             (semiunify (cdr l) (cdr r) s s~ eqn visited)
             (values #f visited))))
      ((var? l); Redex II
       (let ((prev-visit (assp (lambda (x) (var=? x l)) visited)))
         (if prev-visit
             (values (unify (cdr prev-visit) r s) visited)
             (values s (cons `(,l . ,r) visited)))))
      (else (values (and (equal? l r) s) visited)))))

(define (unify u v s s~)
  (let ((u (walk u s s~)) (v (walk v s s~)))
    (cond
      ((and (var? u) (var? v) (var=? u v)) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s s~)))
         (and s (unify (cdr u) (cdr v) s s~))))
      (else (and (equal? u v) s)))))

(define (call/fresh f)
  (lambda (s/c)
    (let ((c (var-no s/c)))
      ((f (var c)) (state (subst s/c) (ssubst s/c) (+ c 1) (eq-no s/c))))))

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
