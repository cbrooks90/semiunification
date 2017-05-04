;; Jason Hemann and Dan Friedman
;; from "μKanren: A Minimal Functional Core for Relational Programming",
;; with bonus semiunification by Chris Brooks

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (and (vector? x1) (equal? x1 x2)))

(define (state s ext vc)
  `(,s ,ext . ,vc))
(define subst car)
(define ext-vars cadr)
(define var-no cddr)

(define (walk u s)
  (let ((pr (and (var? u) (assp (lambda (v) (var=? u v)) s))))
    (if pr (walk (cdr pr) s) u)))

;(define (occurs x v s)
;  (let ((v (walk v s #f)))
;    (cond ((and (var? v) (eq? v x)))
;          ((and (var? v) (var-instance? v x)) (error #f "R-acyclicity violation"))
;          (else (and (pair? v) (or (occurs x (car v) s)
;                                   (occurs x (cdr v) s)))))))

(define (ext-s x v s)
  (cons `(,x . ,v) s))

(define (<= u v)
  (lambda (s/c)
    (let-values (((global local) (semiunify u v (subst s/c) (ext-vars s/c) '())))
      (if s (unit (state global local (var-no s/c))) mzero))))

;(define (== u v)
;  (lambda (s/c)
;    (let-values (((global local) ((s (semiunify u v (subst s/c) #f)))
;      (if s (unit (state s (var-no s/c) (eq-no s/c))) mzero))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (antiunify u v s)
  (let ((u (walk u s #f)) (v (walk v s #f)))
    (cond
      ((and (pair? u) (pair? v))
       (let ((s (antiunify (car u) (car v) s)))
         (antiunify (cdr u) (cdr v) s)))
      ((equal? u v) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      (else
        (let ((x (fresh-var)))
          (ext-s x u (ext-s x v s)))))))

(trace-define (semiunify l r s extern local)
  (let-values (((l l-extern?) (semiwalk l s extern local))
               ((r r-extern?) (semiwalk r s extern local)))
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
      ((f (var c)) (state (subst s/c) (ext-vars s/c) (+ c 1))))))

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
