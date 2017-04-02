(load "miniKanren-wrappers.scm")

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

(test-check 'trival-conjuction
  (run* (q) (fresh (x y) (== q `(,x ,y)) (<= x `(,y . ,y)) (<= x `(,y . (,y . ,y)))))
  '((_.0 _.1)))

(test-check 'bound-variable
  (run* (q) (fresh (x y) (== q `(,x ,y)) (<= `(,y . ,y) x)))
  '(((_.0 . _.0) _.1)))

(test-check 'left-structure-unbound
  (run* (q) (fresh (x y z) (== q `(,x ,y ,z)) (== x `(1 . ,z)) (<= `(,y . ,y) x)))
  '(((1 . 1) _.0 1)))

(test-check 'right-structure-bound-1
  (run* (q) (fresh (x z) (== q `(,x ,z)) (== x `(,z . ,z)) (<= `(1 . 1) x)))
  '(((1 . 1) 1)))

(test-check 'right-structure-bound-2
  (run* (q) (fresh (x z) (== q `(,x ,z)) (<= `(1 . 1) x) (== x `(,z . ,z))))
  '(((1 . 1) 1)))

(test-check 'indirect-right-bind
  (run* (q) (fresh (x y z) (== q `(,x ,y ,z)) (<= `(,y . ,y) x) (== x `(1 . ,z))))
  '(((1 . 1) _.0 1)))

(test-check 'R-acyclicity-failure
  (run* (q) (fresh (x y z) (== q `(,x ,y ,z)) (<= y z) (<= `(f ,x ,x) `(f ,y (f ,z ,z)))))
  '())
