;; Jason Hemann and Dan Friedman

(load "semiKanren.scm")

(define-syntax Zzz
  (syntax-rules ()
    ((_ g) (lambda (s/c) (lambda () (g s/c))))))

(define-syntax conj+
  (syntax-rules ()
    ((_ g) (Zzz g))
    ((_ g0 g ...) (conj (Zzz g0) (conj+ g ...)))))

(define-syntax disj+
  (syntax-rules ()
    ((_ g) (Zzz g))
    ((_ g0 g ...) (disj (Zzz g0) (disj+ g ...)))))

(define-syntax fresh
  (syntax-rules ()
    ((_ () g0 g ...) (conj+ g0 g ...))
    ((_ (x0 x ...) g0 g ...)
     (call/fresh
      (lambda (x0)
        (fresh (x ...) g0 g ...))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) ...) (disj+ (conj+ g0 g ...) ...))))

(define-syntax run
  (syntax-rules ()
    ((_ n (x ...) g0 g ...)
     (map reify-1st (take n (call/goal (fresh (x ...) g0 g ...)))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (map reify-1st (take-all (call/goal (fresh (x ...) g0 g ...)))))))

(define empty-state (state '() '() 0 0))

(define (call/goal g) (g empty-state))

(define (pull $)
  (if (procedure? $) (pull ($)) $))

(define (take-all $)
  (let (($ (pull $)))
    (if (null? $) '() (cons (car $) (take-all (cdr $))))))

(define (take n $)
  (if (zero? n) '()
    (let (($ (pull $)))
      (if (null? $) '() (cons (car $) (take (- n 1) (cdr $)))))))

(define (reify-1st s/c)
  (let ((v (walk* (var 0) (subst s/c) resolves-to?)))
    (walk* v (reify-s v '()) var=?)))

(define (walk* v s proc)
  (let ((v (gen-walk v s proc)))
    (cond
      ((var? v) v)
      ((pair? v) (cons (walk* (car v) s proc)
                   (walk* (cdr v) s proc)))
      (else v))))

(define (reify-s v s)
  (let ((v (gen-walk v s var=?)))
    (cond
      ((var? v)
       (let  ((n (reify-name (length s))))
         (cons `(,v . ,n) s)))
      ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
      (else s))))

(define (reify-name n)
  (string->symbol
    (string-append "_" "." (number->string n))))

(define (fresh/nf n f)
  (letrec
    ((app-f/v*
       (lambda (n v*)
         (cond
           ((zero? n) (apply f (reverse v*)))
           (else (call/fresh
                   (lambda (x)
                     (app-f/v* (- n 1) (cons x v*)))))))))
     (app-f/v* n '())))
