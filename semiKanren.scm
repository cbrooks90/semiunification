(define (var c) (vector c))
(define (var? x) (vector? x))

(define bottom (var '⊥))
(define (bottom? x) (eqv? x bottom))

(define (state s bds) (cons s bds))
(define subst car)
(define bds cdr)
(define empty-state (cons '() '()))

(define (walk u s)
  (let ((pr (and (var? u) (assv u s))))
    (if pr (walk (cdr pr) s) u)))

(define (walk-approx u s bds lower?)
  (let ((orig (walk u s)))
    (let loop ((u orig) (orig orig))
      (cond
       ((and lower? (bottom? u)) orig)
       ((not (or lower? u)) orig)
       ((var? u) (loop (walk ((if lower? car cdr) (bounds u bds)) s) orig))
       (else u)))))

(define (bounds v li)
  (let ((pr (assv v li)))
    (if pr (cdr pr)
        (cons bottom #f))))

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

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
     ((eqv? u v) (values u s))
     ((var? u) (values v (ext-s u v s)))
     ((var? v) (values u (ext-s v u s)))
     ((and (pair? u) (pair? v))
      (let*-values (((t1 s) (unify (car u) (car v) s))
                    ((t2 s) (if s (unify (cdr u) (cdr v) s) (values #f #f))))
        (if s (values (cons t1 t2) s) (values #f #f))))
     (else (values #f #f)))))

;; Helper functions for semiunification

(define (factorize lb ub bds s pairs)
  (let ((lb (walk-approx lb s bds #t)) (ub (walk-approx ub s bds #f)))
    (cond
   ((and (pair? lb) (pair? ub))
    (let*-values (((t1 s bds pairs) (factorize (car lb) (car ub) bds s pairs))
                  ((t2 s bds pairs) (if s (factorize (cdr lb) (cdr ub) bds s pairs)
                                        (values #f #f bds pairs))))
      (values (cons t1 t2) s bds pairs)))
   ((eqv? lb ub) (values lb s bds pairs))
   ((assp (lambda (x) (equal? (cons lb ub) x)) pairs)
    => (lambda (x) (values (cdr x) s bds pairs)))
   (else
    (let-values (((s bds _) (semiunify lb ub s bds '())))
      (if s
          (let ((x (vector 'idk)))
            (values x s (cons (cons x (cons lb ub)) bds)
                    (cons (cons (cons lb ub) x) pairs)))
          (values #f #f bds pairs)))))))

(define (adjust lb ub s bds v vs)
  (if (or (var? lb) (not ub))
      (values s (cons (cons v (cons lb ub)) bds) vs)
      (let-values (((term s bds _) (factorize lb ub bds s '())))
        (values (and s (ext-s v term s)) bds vs))))

(define (antiunify u v)
  (cond
   ((not u) v)
   ((not v) u)
   ((var? u) u)
   ((var? v) v)
   ((and (pair? u) (pair? v))
    (cons (antiunify (car u) (car v)) (antiunify (cdr u) (cdr v))))
   ((eqv? u v) u)
   (else bottom)))

(define (adjust-upper-bound v term s bds vs)
  (let-values (((_ s) (if (assoc v vs) (unify term (cdr (assoc v vs)) s bds) (values #f s))))
    (let ((b (bounds v bds))
          (vs (cons (cons v term) vs)))
      (adjust (car b) (antiunify (cdr b) term) s bds v vs))))

(define (adjust-lower-bound v term s bds vs)
  (let ((b (bounds v bds)))
    (let-values (((term _) (unify (car b) term s bds)))
      (adjust term (cdr b) s bds v vs))))

(define (semiunify l r s bds vs)
  (let ((l (walk l s)) (r (walk r s)))
    (cond
     ((and (var? l) (var? r))
      (let-values (((s bds vs) (adjust-upper-bound l r s bds vs)))
        (adjust-lower-bound r l s bds vs)))
     ((var? l) (adjust-upper-bound l r s bds vs))
     ((and (var? r) (not (bottom? r))) (adjust-lower-bound r l s bds vs))
     ((and (pair? l) (pair? r))
      (let-values (((s bds vs) (semiunify (car l) (car r) s bds vs)))
        (if s (semiunify (cdr l) (cdr r) s bds vs)
            (values #f bds vs))))
     ((eqv? l r) (values s bds vs))
     (else (values #f bds vs)))))

(define (<= u v)
  (lambda (s/b)
    (let-values (((s bds _) (semiunify u v (subst s/b) (bds s/b) '())))
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
  (let ((v (walk-approx v s bds #t)))
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
