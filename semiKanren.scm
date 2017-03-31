;; Jason Hemann and Dan Friedman
;; from "μKanren: A Minimal Functional Core for Relational Programming",
;; with bonus semiunification by Chris Brooks

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (and (vector? x1) (equal? x1 x2)))

(define (state s vc ec)
  `(,s ,vc . ,ec))
(define subst car)
(define var-no cadr)
(define eq-no cdr)

(define (walk u s)
  (let ((pr (and (var? u) (assp (lambda (v) (var=? u v)) s))))
    (if pr (walk (cdr pr) s) u)))

; Might be able to omit since violations of occurs check violate R-acyclicity
(define (occurs x v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) (var=? v x))
      (else (and (pair? v) (or (occurs x (car v) s)
                               (occurs x (cdr v) s)))))))

(define (ext-s x v s)
  (if (occurs x v s #f `((,x . ,v) . ,s))))

(define (<= u v)
  (lambda (s/c)
    (let-values (((s _) (semiunify u v (subst s/c) (eq-no s/c) '())))
      (if s (unit (state s (var-no s/c) (+ (eq-no s/c) 1))) mzero))))

(define (== u v)
  (lambda (s/c)
    (let ((s (unify u v (subst s/c))))
      (if s (unit (state s (var-no s/c) (eq-no s/c))) mzero))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (freshen t eqn)
  (define (aux-var v)
    (list->vector (append (vector->list x) (list eqn))))
  (cond ((var? t) (aux-var t))
        ((pair? t) (map (lambda (x) (freshen x eqn)) t))
        (else t)))

(define (semiunify l r s eqn visited)
  (cond
    ((and (var? r) (not (var? l))); Redex I
     (values (unify r (freshen l) s) visited))
    ((and (pair? l) (pair? r) (eq? (car l) (car r)))
     (let loop ((ls (cdr l)) (rs (cdr r)) (s s) (vs visited))
       (cond
         ((and (null? ls) (null? rs)) (values s vs))
         ((or (null? ls) (null? rs)) (values #f vs))
         (else
           (let-values (((s vs) (semiunify (car ls) (car rs) s eqn vs)))
             (loop (cdr ls) (cdr rs) s vs))))))
    ((var? l)
     (let ((prev-visit (assp (lambda (x) (var=? x l)) visited)))
       (if prev-visit; Redex II
           (unify (cdr prev-visit) r s)
           (values s (cons `(,l . ,r) visited)))))
    (else (values (and (equal? l r) s) visited))))

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((and (var? u) (var? v) (var=? u v)) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (pair? u) (pair? v) (eq? (car l) (car r)))
       (let loop ((us (cdr u)) (vs (cdr v)) (s s) (vs visited))
         (if ((and (null? us) (null? vs)) s)
             ((or (null? us) (null? vs)) #f)
             (let-values (((s vs) (semiunify (car ls) (car rs) s eqn vs)))
               (loop (cdr ls) (cdr rs) s vs)))))
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
