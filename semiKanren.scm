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

(define (resolves-to? u v)
  (let loop ((u (vector->list u)) (v (vector->list v)))
    (cond ((null? v) #t)
          ((null? u) #f)
          ((equal? (car u) (car v)) (loop (cdr u) (cdr v)))
          (else #f))))

(define (gen-walk u s proc)
  (let ((pr (and (var? u) (assp (lambda (v) (proc u v)) s))))
    (if pr (gen-walk (cdr pr) s proc) u)))

(define (walk u s)
  (gen-walk u s resolves-to?))

(define (occurs x v s)
  (let ((v (walk v s)))
    (cond
      ((and (var? v) (eq? v x)))
      ((and (var? v) (resolves-to? v x)) (error #f "R-acyclicity violation"))
      (else (and (pair? v) (or (occurs x (car v) s)
                               (occurs x (cdr v) s)))))))

(define (ext-s x v s aux)
  (cond
    ((occurs x v (append s aux)) #f)
    (else (cons `(,x . ,v) s))))

(define (<= u v)
  (lambda (s/c)
    (let-values (((global local ext)
                  (semiunify u v (subst s/c) '() (ext-vars s/c) (eq-no s/c) #f)))
      (if global
          (unit (state global (append ext local) (var-no s/c) (+ (eq-no s/c) 1)))
          mzero))))

(define (== u v)
  (lambda (s/c)
    (let ((s (unify u v (subst s/c) '() #f)))
      (if s (unit (state s (ext-vars s/c) (var-no s/c) (eq-no s/c))) mzero))))

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
          (values x (cons (cons (cons u v) x) a-s)))))))

(define (freshen t s eqn)
  (let ((t (walk t s)))
    (cond
      ((var? t)
       (let ((li (vector->list t)))
         (list->vector (append li (list eqn)))))
      ((pair? t)
       (cons (freshen (car t) s eqn)
             (freshen (cdr t) s eqn)))
      (else t))))

(define (semiunify l r s local ext eqn test?)
  (let* ((l (walk l s))
         (local-l (walk l local))
         (r (walk r s))
         (local-r (walk r local)))
    (cond
      ((and (var? l) (var? r) (or test? (var=? l r))) (values s local ext))
      ((not (eq? l local-l))
       (post l r (unify local-l r s local eqn) local ext eqn))
      ((not (eq? r local-r))
       (let-values (((s local ext)
                     (semiunify l local-r (ext-s r (freshen l (append s local) eqn) s local)
                                local ext eqn test?)))
         (post l r s local ext eqn)))
      ((var? r) (post l r (ext-s r (freshen l (append s local) eqn) s local) local ext eqn))
      ((var? l) (post l r s (ext-s l r local s) ext eqn))
      ((and (pair? l) (pair? r))
       (let-values (((s local ext) (semiunify (car l) (car r) s local ext eqn test?)))
         (if s (semiunify (cdr l) (cdr r) s local ext eqn test?) (values #f '() '()))))
      ((equal? l r) (values s local ext))
      (else (values #f '() '())))))

(define (post l r s local ext eqn)
  (let ((l~ (walk l ext))
        (r~ (walk r ext)))
    (cond
      ((not (eq? l l~))
       (let-values (((t _) (antiunify l~ r~ (append s local ext) '())))
         (values s local (ext-s l t ext '()))))
      ((not (eq? r r~))
       (let-values (((new ls ext) (semiunify l~ r~ s '() '() eqn #t)))
         ; I think this is too much. Need to check that antiunification vars are not bound
         (if (eq? new s)
             (values (ext-s r (freshen l~ (append s local) eqn) s local)
                     (append ls local) ext)
             (values #f '() '()))))
      (else (values s local ext)))))

(define (unify u v s local eqn)
  (let ((u (walk u (append s local))) (v (walk v (append s local))))
    (cond
      ((and (var? u) (var? v) (var=? u v)) s)
      ((var? u) (ext-s u v s local))
      ((var? v) (ext-s v u (if eqn (ext-s (freshen v '() eqn) u s local) s) local))
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s local eqn)))
         (and s (unify (cdr u) (cdr v) s local eqn))))
      ((equal? u v) s)
      (else #f))))

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
