(define (var c) (vector c))
(define (var? x) (vector? x))

(define bottom '⊥)
(define (bottom? x) (eqv? x bottom))

(define top '⊤)
(define (top? x) (eqv? x top))

(define (state s bds) (cons s bds))
(define subst car)
(define bds cdr)
(define empty-state (cons '() '()))

(define (walk u s)
  (let ((pr (and (var? u) (assv u s))))
    (if pr (walk (cdr pr) s) u)))

;; Do we need to walk the individual bounds?
(define (bounds v li)
  (let ((pr (assv v li)))
    (if pr (cdr pr)
        (cons bottom top))))

(define (occurs x v s)
  (let ((v (walk v s)))
    (cond
     ((var? v) (eqv? v x))
     ((pair? v) (or (occurs x (car v) s) (occurs x (cdr v) s)))
     (else #f))))

(define (ext-s x v s)
  (cond
   #;((occurs x v s))
   (else (cons `(,x . ,v) s))))

(define (old-unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
     ((eqv? u v) s)
     ((var? u) (ext-s u v s))
     ((var? v) (ext-s v u s))
     ((and (pair? u) (pair? v))
      (let ((s (old-unify (car u) (car v) s)))
        (and s (old-unify (cdr u) (cdr v) s))))
     (else #f))))

;; Helper functions for semiunification

(define (antiunify u v)
  (cond
   ((top? u) v)
   ((top? v) u)
   ((or (var? u) (bottom? u)) u)
   ((or (var? v) (bottom? v)) v)
   ((and (pair? u) (pair? v))
    (cons (antiunify (car u) (car v)) (antiunify (cdr u) (cdr v))))
   ((eqv? u v) u)
   (else bottom)))

(define (unify u v s)
  (cond
   ((eqv? u v) u)
   ((or (var? u) (bottom? u)) v)
   ((or (var? v) (bottom? v)) u)
   ((and (pair? u) (pair? v))
    (let ((t (unify (car u) (car v) s)))
      (and t (cons t (unify (cdr u) (cdr v) s)))))
   (else #f)))

;; Might still need to make a fresh variable for bounds which aren't equal
(define (adjust lb ub s bds v vs)
  (if (or (var? lb) (bottom? lb) (top? ub))
      (values v s (cons (cons v (cons lb ub)) bds) vs)
      (let-values (((t s bds _) (semiunify lb ub s bds '())))
        (values t (and s (ext-s v t s)) bds vs))))

;; I'm not sure if this will work correctly when unifying three or more terms in an equation
(define (adjust-upper-bound v term s bds vs)
  (let ((s (if (assoc v vs) (old-unify term (cdr (assoc v vs)) s) s)))
    (let ((b (bounds v bds))
          (vs (cons (cons v term) vs)))
      (adjust (car b) (antiunify (cdr b) term) s bds v vs))))

(define (adjust-lower-bound v term s bds vs)
  (let ((b (bounds v bds)))
    (adjust (unify (car b) term s) (cdr b) s bds v vs)))

(define (semiunify l r s bds vs)
  (let ((l (walk l s)) (r (walk r s)))
    (cond
     ((or (eqv? l r) (bottom? l) (top? r)) (values l s bds vs))
     ((and (var? l) (var? r))
      ;; I wonder if we can get away with only updating upper bounds here
      (let-values (((t s bds vs) (adjust-lower-bound r l s bds vs)))
        (adjust-upper-bound l r s bds vs)))
     ((var? l) (adjust-upper-bound l r s bds vs))
     ((and (var? r) (not (pair? l)))
      (semiunify l (cdr (bounds r bds)) (ext-s r l s) bds vs))
     ((var? r) (adjust-lower-bound r l s bds vs))
     ((and (pair? l) (pair? r))
      (let*-values (((t1 s bds vs) (semiunify (car l) (car r) s bds vs))
                    ((t2 s bds vs) (if s (semiunify (cdr l) (cdr r) s bds vs)
                                       (values #f #f bds vs))))
        (values (cons t1 t2) s bds vs)))
     (else (values #f #f bds vs)))))

(define (<= u v)
  (lambda (s/b)
    (let-values (((t s bds _) (semiunify u v (subst s/b) (bds s/b) '())))
      (if s (cons (state s bds) '()) '()))))

(define (== u v)
  (conj2 (<= u v) (<= v u)))

;; The following code is from The Reasoned Schemer, 2nd ed. with license reproduced below:

;; Copyright © 2018 Daniel P. Friedman, William E. Byrd, Oleg Kiselyov, and Jason Hemann

;; Permission is hereby granted, free of charge, to any person obtaining a copy of this
;; software and associated documentation files (the “Software”), to deal in the Software
;; without restriction, including without limitation the rights to use, copy, modify,
;; merge, publish, distribute, sublicense, and/or sell copies of the Software, and to
;; permit persons to whom the Software is furnished to do so, subject to the following
;; conditions:

;; The above copyright notice and this permission notice shall be included in all copies
;; or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
;; INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
;; PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF
;; CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE
;; OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(define (append-inf s-inf t-inf)
  (cond
   ((null? s-inf) t-inf)
   ((pair? s-inf)
    (cons (car s-inf)
      (append-inf (cdr s-inf) t-inf)))
   (else (lambda ()
           (append-inf t-inf (s-inf))))))

(define (append-map-inf g s-inf)
  (cond
   ((null? s-inf) '())
   ((pair? s-inf)
    (append-inf (g (car s-inf))
      (append-map-inf g (cdr s-inf))))
   (else (lambda () (append-map-inf g (s-inf))))))

(define (conj2 g1 g2)
  (lambda (s/b)
    (append-map-inf g2 (g1 s/b))))

(define-syntax conj
  (syntax-rules ()
    ((conj) (lambda (s/b) `(,s/b)))
    ((conj g) g)
    ((conj g0 g ...) (conj2 g0 (conj g ...)))))

(define (call/fresh name f)
  (f (var name)))

(define-syntax fresh
  (syntax-rules ()
    ((fresh () g ...) (conj g ...))
    ((fresh (x0 x ...) g ...)
     (call/fresh 'x0
       (lambda (x0)
         (fresh (x ...) g ...))))))

(define (reify-name n)
  (string->symbol
   (string-append "_" (number->string n))))

(define (reify-s v r)
  (let ((v (walk v r)))
    (cond
     ((var? v)
      (let* ((n (length r))
             (rn (reify-name n)))
        (cons `(,v . ,rn) r)))
     ((pair? v)
      (reify-s (cdr v) (reify-s (car v) r)))
     (else r))))

(define (walk* v s bds)
  (let ((v (walk v s)))
    (cond
     ((var? v) v)
     ((pair? v) (cons (walk* (car v) s bds) (walk* (cdr v) s bds)))
     (else v))))

(define (reify v s bds)
  (let* ((v (walk* v s bds))
         (r (reify-s v '())))
    (walk* v r bds)))

(define (take-inf n s-inf)
  (cond
   ((and n (zero? n)) '())
   ((null? s-inf) '())
   ((pair? s-inf)
    (cons (car s-inf)
      (take-inf (and n (- n 1)) (cdr s-inf))))
   (else (take-inf n (s-inf)))))

(define (run-goal n g)
  (take-inf n (g empty-state)))

(define-syntax run
  (syntax-rules ()
    ((run n (x0 x ...) g ...)
     (run n q (fresh (x0 x ...)
                (== `(,x0 ,x ...) q) g ...)))
    ((run n q g ...)
     (let ((q (var 'q)))
       (map (lambda (s/b) (reify q (subst s/b) (bds s/b)))
         (run-goal n (conj g ...)))))))

(define-syntax run*
  (syntax-rules ()
    ((run* q g ...) (run #f q g ...))))
