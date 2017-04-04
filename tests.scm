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

(test-check 'trivial-conjunction
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= x `(,y . ,y))
      (<= x `(,y . (,y . ,y)))))
  '((_.0 _.1)))

(test-check 'bound-variable
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= `(,y . ,y) x)))
  '(((_.0 . _.0) _.1)))

(test-check 'right-structure-bound-1
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (== x `(,y . ,y))
      (<= `(1 . 1) x)))
  '(((1 . 1) 1)))

(test-check 'right-structure-bound-2
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= `(1 . 1) x)
      (== x `(,y . ,y))))
  '(((1 . 1) 1)))

(test-check 'indirect-right-bind-1
  (run* (q)
    (fresh (x y z)
      (== q `(,x ,y ,z))
      (== x `(1 . ,z))
      (<= `(,y . ,y) x)))
  '(((1 . 1) _.0 1)))

(test-check 'indirect-right-bind-2
  (run* (q)
    (fresh (x y z)
      (== q `(,x ,y ,z))
      (<= `(,y . ,y) x)
      (== x `(1 . ,z))))
  '(((1 . 1) _.0 1)))

(test-check 'concrete-variable-check-1
  (run* (q)
    (fresh (x y z w)
      (== q `(,x ,y ,z ,w))
      (<= `(f ,x ,x) `(f ,y ,w))
      (<= y z)
      (<= 2 x)))
  '((2 2 2 2)))

(test-check 'concrete-variable-check-2
  (run* (q)
    (fresh (x y z w)
      (<= 2 x)
      (== q `(,x ,y ,z ,w))
      (<= `(f ,x ,x) `(f ,y ,w))
      (<= y z)))
  '((2 2 2 2)))

(test-check 'R-acyclicity-failure-1
  (run* (q)
    (fresh (x y z)
      (== q `(,x ,y ,z))
      (<= y z)
      (<= `(f ,x ,x) `(f ,y (f ,z ,z)))))
  '())

(test-check 'R-acyclicity-failure-2
  (run* (q)
    (fresh (x y z)
      (== q `(,x ,y ,z))
      (<= `(f ,x ,x) `(f ,y (f ,z ,z)))
      (<= y z)))
  '())
