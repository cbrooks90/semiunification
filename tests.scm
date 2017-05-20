(load "miniKanren-wrappers.scm")
(load "test-check.scm")

;; Antiunification tests

(test-check 'local-antiunify-1
  (run* (q)
    (fresh (x y z)
      (== q `(,x ,y ,z))
      (<= x 1)
      (<= x 2)
      (<= `(f ,x ,x) `(f (f 3 4) (f ,y ,z)))))
  '((_.0 3 4)))

(test-check 'local-antiunify-2
  (run* (q)
    (fresh (x y z)
      (== q `(,x ,y ,z))
      (<= x 1)
      (<= x 2)
      (<= `(f (f 3 4) (f ,y ,z)) `(f ,x ,x))))
  '(((f 3 4) _.0 _.1)))

(test-check 'local-antiunify-3
  (run* (q)
    (fresh (x y z)
      (== q `(,x ,y ,z))
      (<= x 1)
      (<= x 2)
      (<= `(f ,x (f ,y ,z)) `(f (f 3 4) ,x))))
  '(((f _.0 _.1) _.2 _.3)))

(test-check 'antiunify-1
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= x 17)
      (<= y x)
      (<= x 83)))
  '((_.0 _.1)))

(test-check 'antiunify-2
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= y x)
      (<= x 17)
      (<= x 83)))
  '((_.0 _.1)))

(test-check 'antiunify-3
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= x 17)
      (<= x 83)
      (<= y x)))
  '((_.0 _.1)))

(test-check 'antiunify-4
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= x '(f 1))
      (<= x '(f 2))
      (<= `(f ,y) x)))
  '(((f _.0) _.1)))

(test-check 'antiunify-5
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= x '(f 1))
      (<= x '(f 2))
      (<= y x)))
  '((_.0 _.1)))

(test-check 'antiunify-6
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= `(f ,x) '(f 1))
      (<= `(f ,x) '(f 2))
      (<= y x)))
  '((_.0 _.1)))

(test-check 'antiunify-fail-1
  (run* (x)
    (<= x 17)
    (<= x 83)
    (<= 41 x))
  '())

(test-check 'antiunify-fail-2
  (run* (x)
    (<= x 17)
    (<= 41 x)
    (<= x 83))
  '())

(test-check 'antiunify-fail-3
  (run* (x)
    (<= 41 x)
    (<= x 17)
    (<= x 83))
  '())

(test-check 'antiunify-fail-4
  (run* (x)
    (<= x '(f 1))
    (<= x '(f 2))
    (<= 3 x))
  '())

(test-check 'antiunify-fail-5
  (run* (x)
    (<= x '(f 1))
    (<= x '(f 2))
    (<= '(f 4) x))
  '())

(test-check 'antiunify-fail-6
  (run* (x)
    (<= `(f ,x) '(f 1))
    (<= `(f ,x) '(f 2))
    (<= 4 x))
  '())

(test-check 'antiunify-fail-7
  (run* (x)
    (<= `(f ,x) '(f 1))
    (<= `(g ,x) '(g 2))
    (<= 2 x))
  '())

;; Other tests

(test-check 'trivial-conjunction
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= x `(,y . ,y))
      (<= x `(,y . (,y . ,y)))))
  '((_.0 _.1)))

; There should be a difference between unbound and no constraint. Ask about this.
(test-check 'bound-variable
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= `(,y . ,y) x)))
  '(((_.0 . _.0) _.1)))

(test-check 'indirect-unify-1
  (run* (q)
    (fresh (x y z w)
      (== q `(,x ,y ,z ,w))
      (<= `(f ,w ,x ,x) `(f ,y (f 3 4) (f ,z ,w)))))
  '((_.0 4 3 4)))

(test-check 'indirect-unify-2
  (run* (q)
    (fresh (x y z w)
      (== q `(,x ,y ,z ,w))
      (<= `(f ,w ,x ,x) `(f ,y (f 3 4) (f ,z ,y)))))
  '((_.0 4 3 _.1)))

(test-check 'local-chain
  (run* (q)
    (fresh (a b c d e f g h)
      (== q `(,a ,b ,c ,d ,e ,f ,g ,h))
      (<= `(f ,a ,b ,c ,d ,e ,f ,g 9) `(f ,b ,c ,d ,e ,f ,g ,h ,d))))
  '((_.0 _.1 _.2 9 9 9 9 9)))

(test-check 'local-vs-nonlocal
  (run* (q)
    (fresh (x y z)
      (== q `(,x ,y ,z))
      (<= `(f ,x (f ,y ,z)) `(f (g 3 4) ,x))))
  '())

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

(test-check 'right-structure-unbound-1
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= `(,y . ,y) x)
      (<= `(1 . 1) x)))
  '(((1 . 1) _.0)))

(test-check 'right-structure-unbound-2
  (run* (q)
    (fresh (x y)
      (== q `(,x ,y))
      (<= `(1 . 1) x)
      (<= `(,y . ,y) x)))
  '(((1 . 1) _.0)))

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

;(test-check 'R-acyclicity-failure-1
;  (run* (q)
;    (fresh (x y z)
;      (== q `(,x ,y ,z))
;      (<= y z)
;      (<= `(f ,x ,x) `(f ,y (f ,z ,z)))))
;  '())

;(test-check 'R-acyclicity-failure-2
;  (run* (q)
;    (fresh (x y z)
;      (== q `(,x ,y ,z))
;      (<= `(f ,x ,x) `(f ,y (f ,z ,z)))
;      (<= y z)))
;  '())
