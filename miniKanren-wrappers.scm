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

(define empty-state (state '() 0 0))

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
  (let ((v (walk* (var 0) (subst s/c))))
    (walk* v (reify-s v '()))))

(define (walk* v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) v)
      ((pair? v) (cons (walk* (car v) s)
                   (walk* (cdr v) s)))
      (else  v))))

(define (reify-s v s)
  (let ((v (walk v s)))
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

;; Test programs

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
                     "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
                     'tested-expression expected produced)))))))

(test-check #f
  (run* (q) (fresh (x y) (== q `(,x ,y)) (<= x `(,y . ,y)) (<= x `(,y . (,y . ,y)))))
  '((_.0 _.1)))

(test-check #f
  (run* (q) (fresh (x y) (== q `(,x ,y)) (<= `(,y . ,y) x)))
  '(((_.0 . _.0) _.1)))

(test-check #f
  (run* (q) (fresh (x y z) (== q `(,x ,y ,z)) (== x `(1 . ,z)) (<= `(,y . ,y) x)))
  '(((1 . 1) _.0 1)))

(test-check #f
  (run* (q) (fresh (x z) (== q `(,x ,z)) (== x `(,z . ,z)) (<= `(1 . 1) x)))
  '(((1 . 1) 1)))

(test-check #f
  (run* (q) (fresh (x z) (== q `(,x ,z)) (<= `(1 . 1) x) (== x `(,z . ,z))))
  '(((1 . 1) 1)))

(test-check #f
  (run* (q) (fresh (x y z) (== q `(,x ,y ,z)) (<= `(,y . ,y) x) (== x `(1 . ,z))))
  '(((1 . 1) _.0 1)))
