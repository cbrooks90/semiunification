;; Jason Hemann and Dan Friedman
;; from "μKanren: A Minimal Functional Core for Relational Programming",
;; with bonus semiunification by Chris Brooks

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (and (vector? x1) (equal? x1 x2)))

(define (state s ext vc ec)
  `(,s ,ext ,vc . ,ec))
(define subst car)
(define ext-vars cadr)
(define var-no caddr)
(define eq-no cdddr)

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
    (let*-values (((s ext eqn) (values (subst s/c) (ext-vars s/c) (eq-no s/c)))
                  ((global local) (semiunify u v s ext '() eqn)))
      (if global (unit (state global (append local ext) (var-no s/c) (+ eqn 1))) mzero))))

(define (== u v)
  (lambda (s/c)
    (let*-values (((s ext eqn) (values (subst s/c) (ext-vars s/c) (eq-no s/c)))
                  ((global local) (semiunify u v s ext '() eqn))
                  ((global local) (semiunify v u global (append local ext) '() (+ eqn 1))))
      (if global (unit (state global (append local ext) (var-no s/c) (+ eqn 2))) mzero))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (antiunify u v s a-s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((and (pair? u) (pair? v))
       (let*-values (((t1 a-s) (antiunify (car u) (car v) s a-s))
                     ((t2 a-s) (antiunify (cdr u) (cdr v) s a-s)))
         (values (cons t1 t2) a-s)))
      ((equal? u v) (values u a-s))
      ((assp (lambda (x) (equal? (cons u v) x)) a-s)
       => (lambda (x) (values (cdr x) a-s)))
      (else
        (let ((x (vector 'x)))
          (values x (ext-s (cons u v) x a-s)))))))

(define (freshen t s eqn)
  (let ((t (walk t s)))
    (cond
      ((var? t)
       (let ((li (vector->list t)))
         (list->vector (append li (list eqn)))))
      ((pair? t)
       (cons (freshen (car t) s eqn)
             (freshen (cdr t) s eqn)))
      (else  t))))

;(l-extern
;        (let-values (((t _) (antiunify l r (append s local extern) '())))
;          (values s (ext-s l-extern t local))))
;      (r-extern (let-values (((new ls) (semiunify l r s extern local eqn)))
;                  (if (eq? new s)
;                      (values (ext-s r-extern (freshen l (append s local) eqn) s)
;                              (append ls local))
;                      (values #f #f))))

(define (semiwalk t s local local?)
  (cond [(assp (lambda (v) (var=? t v)) s)
         => (lambda (x) (semiwalk (cdr x) s local local?))]
        [(assp (lambda (v) (var=? t v)) local)
         => (lambda (x) (semiwalk (cdr x) s local #t))]
        [else (values t local?)]))

(define (semiunify l r s local eqn)
  (let-values
    (((l local-l?) (semiwalk l s local #f))
     ((r local-r?) (semiwalk r s local #f)))
    (cond
      ((and (var? l) (var? r) (var=? l r)) (values s local))
      ((var? l) (values s (ext-s l r local)))
      ((var? r) (values (ext-s r (freshen l (append s local) eqn) s) local))
      ((and (pair? l) (pair? r))
       (let-values (((s local) (semiunify (car l) (car r) s extern local eqn)))
         (if s (semiunify (cdr l) (cdr r) s extern local eqn) (values #f #f))))
      ((equal? l r) (values s local))
      (else (values #f #f)))))

(define (call/fresh f)
  (lambda (s/c)
    (let ((c (var-no s/c)))
      ((f (var c)) (state (subst s/c) (ext-vars s/c) (+ c 1) (eq-no s/c))))))

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
