(load "semiKanren.scm")

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

#;(test-check 'three-way-unify-1
  (run* (a b x y z w)
    (<= `(f ,x (g ,x) ,y) `(f (h ,z 3 ,a) (g (h 52 ,w ,b)) (h 52 3 99)))
    (== y x))
  '((99 99 (h 52 3 99) (h 52 3 99) 52 3)))

(begin
;; Antiunification tests

(test-check 'local-antiunify-1
  (run* (x y z)
    (<= x 1)
    (<= x 2)
    (<= `(f ,x ,x) `(f (f 3 4) (f ,y ,z))))
  '((_0 3 4)))

(test-check 'local-antiunify-2
  (run* (x y z)
    (<= x 1)
    (<= x 2)
    (<= `(f (f 3 4) (f ,y ,z)) `(f ,x ,x)))
  '())

(test-check 'local-antiunify-3
  (run* (x y z)
    (<= x 1)
    (<= x 2)
    (<= `(f ,x (f ,y ,z)) `(f (f 3 4) ,x)))
  '())

(test-check 'antiunify-1
  (run* (x y)
    (<= x 17)
    (<= y x)
    (<= x 83))
  '((_0 _1)))

(test-check 'antiunify-2
  (run* (x y)
    (<= y x)
    (<= x 17)
    (<= x 83))
  '((_0 _1)))

(test-check 'antiunify-3
  (run* (x y)
    (<= x 17)
    (<= x 83)
    (<= y x))
  '((_0 _1)))

(test-check 'antiunify-4
  (run* (x y)
    (<= x '(f 1))
    (<= x '(f 2))
    (<= `(f ,y) x))
  '(((f _0) _1)))

(test-check 'antiunify-5
  (run* (x y)
    (<= x '(f 1))
    (<= x '(f 2))
    (<= y x))
  '((_0 _1)))

(test-check 'antiunify-6
  (run* (x y)
    (<= `(f ,x) '(f 1))
    (<= `(f ,x) '(f 2))
    (<= y x))
  '((_0 _1)))

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
  (run* (x y)
    (<= x `(,y . ,y))
    (<= x `(,y . (,y . ,y))))
  '((_0 _1)))

(test-check 'bound-variable
  (run* (x y)
    (<= `(,y . ,y) x))
  '(((_0 . _0) _1)))

(test-check 'indirect-unify-1
  (run* (x y z w)
    (<= `(f ,w ,x ,x) `(f ,y (f 3 4) (f ,z ,w))))
  '((_0 4 3 4)))

(test-check 'indirect-unify-2
  (run* (x y z w)
    (<= `(f ,w ,x ,x) `(f ,y (f 3 4) (f ,z ,y))))
  '((_0 4 3 _1)))

(test-check 'three-way-unify-1
  (run* (a b x y z w)
    (<= `(f ,x (g ,x) ,y) `(f (h ,z 3 ,a) (g (h 52 ,w ,b)) (h 52 3 99)))
    (== y x))
  '((99 99 (h 52 3 99) (h 52 3 99) 52 3)))

(test-check 'three-way-unify-2
  (run* (a b x y z w)
    (<= `(f ,x (g ,x) ,y) `(f (h ,z 3 ,a) (g (h 52 ,w ,b)) (h 52 3 ,b)))
    (== y x))
  '((_0 _0 (h 52 3 99) (h 52 3 99) 52 3)))

(test-check 'non-three-way-unify
  (run* (a b c d x y)
    (<= `(f ,x ,y) `(f (g ,a ,b) (h (g 3 4) (g ,c ,d))))
    (<= `(h ,x ,x) y))
  '((_0 _1 3 4 _2 (h _3 _3))))

(test-check 'local-chain
  (run* (a b c d e f g h)
    (<= `(f ,a ,b ,c ,d ,e ,f ,g 9) `(f ,b ,c ,d ,e ,f ,g ,h ,d)))
  '((_0 _1 _2 9 9 9 9 9)))

(test-check 'lower-bound-chain
  (run* (a b c d e f g)
    (<= a b)
    (<= b c)
    (<= c d)
    (<= d e)
    (<= e f)
    (<= f g)
    (== a 17))
  '((17 17 17 17 17 17 17)))

(test-check 'lower-bound-chain-fail
  (run* (a b c d e f g)
    (<= a b)
    (<= b c)
    (<= c d)
    (<= d e)
    (<= e f)
    (<= f g)
    (== a 2)
    (== e 3))
  '())

(test-check 'upper-bound-chain-fail
  (run* (a b c d e f g)
    (<= a b)
    (<= b c)
    (<= c d)
    (<= d e)
    (<= e f)
    (<= f g)
    (== e 2)
    (== a 3))
  '())

(test-check 'update-middle-of-chain
  (run* (a b c d)
    (fresh (x y)
      (<= a b)
      (<= b c)
      (<= c d)
      (== a `(f ,x ,y))
      (== b `(f 32 71))))
  '(((f _0 _1) (f 32 71) (f 32 71) (f 32 71))))

(test-check 'local-vs-nonlocal-separate
  (run* (x y z)
    (<= x '(g 3 4))
    (<= `(f 3 4) x))
  '())

(test-check 'local-vs-nonlocal-together-1
  (run* (x y z)
    (<= `(h ,x (f ,y ,z)) `(h (g 3 4) ,x)))
  '())

(test-check 'local-vs-nonlocal-together-2
  (run* (x y z)
    (<= `(h ,x (f 3 4)) `(h (f ,y ,z) ,x)))
  '(((f 3 4) 3 4)))

(test-check 'local-vs-nonlocal-together-3
  (run* (x y z)
    (<= `(h (f ,y ,z) ,x) `(h ,x (g 3 4))))
  '())

(test-check 'local-vs-nonlocal-together-4
  (run* (x y z)
    (<= `(h ,x (f ,y ,z)) `(h (f 17 18) ,x)))
  '(((f _0 _1) _2 _3)))

(test-check 'right-structure-bound-1
  (run* (x y)
    (== x `(,y . ,y))
    (<= `(1 . 1) x))
  '(((1 . 1) 1)))

(test-check 'right-structure-bound-2
  (run* (x y)
    (<= `(1 . 1) x)
    (== x `(,y . ,y)))
  '(((1 . 1) 1)))

(test-check 'right-structure-unbound-1
  (run* (x y)
    (<= `(,y . ,y) x)
    (<= `(1 . 1) x))
  '(((1 . 1) _0)))

(test-check 'right-structure-unbound-2
  (run* (x y)
    (<= `(1 . 1) x)
    (<= `(,y . ,y) x))
  '(((1 . 1) _0)))

(test-check 'indirect-right-bind-1
  (run* (x y z)
    (== x `(1 . ,z))
    (<= `(,y . ,y) x))
  '(((1 . 1) _0 1)))

(test-check 'indirect-right-bind-2
  (run* (x y z)
    (<= `(,y . ,y) x)
    (== x `(1 . ,z)))
  '(((1 . 1) _0 1)))

(test-check 'concrete-variable-check-1
  (run* (x y z w)
    (<= `(f ,x ,x) `(f ,y ,w))
    (<= y z)
    (<= 2 x))
  '((2 2 2 2)))

(test-check 'concrete-variable-check-2
  (run* (x y z w)
    (<= 2 x)
    (<= `(f ,x ,x) `(f ,y ,w))
    (<= y z))
  '((2 2 2 2)))

;; Occurs check tests

(test-check 'R-acyclicity-failure-1
  (run* (x y z)
    (<= y z)
    (<= `(f ,x ,x) `(f ,y (f ,z ,z))))
  '())

(test-check 'R-acyclicity-failure-2
  (run* (x y z)
    (<= `(f ,x ,x) `(f ,y (f ,z ,z)))
    (<= y z))
  '())

(test-check 'simple-cycle-1
  (run* (z)
    (fresh (y)
      (<= `(f ,z ,z) y)
      (<= y z)))
  '())

(test-check 'simple-cycle-2
  (run* (z)
    (fresh (y)
      (<= y z)
      (<= `(f ,z ,z) y)))
  '())

(test-check 'occurs-false-positive-1
  (run* (x)
    (fresh (y z)
      (<= x (cons y z))
      (<= x y)))
  '(_0))

(test-check 'occurs-false-positive-2
  (run* (x)
    (fresh (y z)
      (<= x y)
      (<= x (cons y z))))
  '(_0)))
