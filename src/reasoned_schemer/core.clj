(ns reasoned-schemer.core
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :as l :refer [run* run s# u# == fresh conde]]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; 1. Playthings
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

false ;; #t
true  ;; #f

;; a goal that succeeds
;; "succeed"
s#
;; => #function[clojure.core.logic/succeed]

;; a goal that fails; it is unsuccessful
;; "fail"
u#
;; => #function[clojure.core.logic/fail]

;; run expressions have the value '() when all goals fail
(run* [q]
  u#)
;; => ()

;; q is associated with `true` if `==` (unification) succeeds
(run* [q]
  (== true q))
;; => (true)

;; This expression has the value `()` if the goals fail
(run* [q]
  u#  ;; fail
  (== true q))
;; => ()

(run* [q]
  s#  ;; succeed
  (== true q))
;; => (true)

(run* [q]
  s#
  (== 'corn q))
;; => (corn)

(run* [q]
  u#
  (== 'corn q))
;; => ()

(run* [q]
  s#
  (== false q))
;; => (false)

;; fails because `true` is not equal to `false`
(run* [x]
  (let [x true]
    (== x false)))
;; => ()

;; A variable is "fresh" when it has no association
;; Both q and x start out as fresh here
(run* [q]
  (fresh [x]
    (== x true)
    (== true q)))
;; => (true)

;; The order of arguments to `==` does not matter
(run* [q]
  (fresh [x]
    (== true x)
    (== q true)))
;; => (true)

;; `_0` is a symbol representing a fresh variable
(run* [x]
  s#)
;; => (_0)

(run* [x]             ;; new x introduced
  (let [x false]      ;; new x introduced, shadows previous
    (fresh [x]        ;; new x introduced, shadows previous
      (== true x))))
;; => (_0)

;; For each fresh variable, there is a symbol with an underscore followed by a
;; numeric subscript.
(run* [r]
  (fresh [x y]
    (== (cons x (cons y '())) r)))
;; => ((_0 _1))

(run* [r]
  (fresh [t u]
    (== (cons t (cons u '())) r)))
;; => ((_0 _1))

(run* [r]
  (fresh [x]
    (let [y x]
      (fresh [x]  ;; Within this fresh block, x and y are different variables
        (== (cons y (cons x (cons y '()))) r)))))
;; => ((_0 _1 _0))

;; Reifying r's value reifies the fresh variables in the order in which they
;; appear in the list
;; Note that x and y have been swapped in this example from the previous
;; yet the result remains the same
(run* [r]
  (fresh [x]
    (let [y x]
      (fresh [x]
        (== (cons x (cons y (cons x '()))) r)))))
;; => ((_0 _1 _0))

(run* [q]
  (== true q)
  (== false q))  ;; q is no longer fresh here
;; => ()

(run* [q]
  (== false q)  ;; q is fresh here, so unification succeeds
  (== false q)) ;; q is no longer fresh, but is already associated with `false`: success!
;; => (false)

(run* [q]
  (let [x q]       ;; q and x are now the same
    (== x true)))
;; => (true)

;; When one variable is associated with another, they are said to "co-refer"
;; or "share"
(run* [q]
  (fresh [x]
    (== q x)))   ;; x and q "co-refer", or "share"
;; => (_0)

;; q starts out fresh and then gets x's association
(run* [q]
  (fresh [x]
    (== true x)
    (== q x)))
;; => (true)

(run* [q]
  (fresh [x]
    (== q x)       ;; ensures that whatever association x gets, q also gets
    (== true x)))
;; => (true)


;; The next two examples show that:
;;
;; Every variable introduced by `fresh` (or `run`) is different from every other
;; variable introduced by `fresh` (or `run`)

(run* [q]
  (fresh [x]
    (== (= x q) q)))
;; => (false)

(run* [q]
  (let [x q]            ;; `let` makes x and q the same variable
    (fresh [q]          ;; `fresh` introduces a new variable
      (== (= x q) x))))
;; => (false)

(cond
  false true
  :else false)
;; => false

(cond
  false s#
  :else u#)
;; => #function[clojure.core.logic/fail]

;; NOTE: core.logic's `conde` does not support the else clause, so instead we
;; just use (s# ...)

;; Does not succeed, because the question of the first `conde` line is the goal
;; u# (fail)
;; (conde
;;  (u# s#)
;;  (s# u#))
;; => fail

;; Succeeds, because the question of the first conde line is the goal u#, so
;; `conde` tries the second line, which succeeds
;; (conde
;;  (u# u#)
;;  (s# s#))
;; => success

(run* [x]
  (conde
   ((== 'olive x) s#)  ;; succeeds, resulting in success
   ((== 'oil x)   s#)  ;; refreshes x, then succeeds, resulting in success
   (s# u#)))           ;; No more goals succeed, we're done
;; => (olive oil)

;; The "e" in `conde` stands for "every line", since every line can succeed

;; (run n ...) produces at most n values
(run 1 [x]
  (conde
   ((== 'olive x) s#)
   ((== 'oil x) s#)
   (s# u#)))
;; => (olive)

(run* [x]
  (conde
   ((== 'virigin x) u#)  ;; This line fails, and is as if it were never there
   ((== 'olive x) s#)
   (s# s#)               ;; Succeeds without x getting an association
   ((== 'oil x) s#)
   (s# u#)))
;; => (olive _0 oil)

;; First two values only
(run 2 [x]
  (conde
   ((== 'extra x) s#)
   ((== 'virgin x) u#)
   ((== 'olive x) s#)
   ((== 'oil x) s#)
   (s# u#)))
;; => (extra olive)

(run* [r]
  (fresh [x y]
    (== 'split x)
    (== 'pea y)
    (== (cons x (cons y '())) r)))
;; => ((split pea))

(run* [r]
  (fresh [x y]
    (conde
     ((== 'split x) (== 'pea y))
     ((== 'navy x)  (== 'bean y))
     (s# u#))
    (== (cons x (cons y '())) r)))
;; => ((split pea) (navy bean))

(run* [r]
  (fresh [x y]
    (conde
     ((== 'split x) (== 'pea y))
     ((== 'navy x)  (== 'bean y))
     (s# u#))
    (== (cons x (cons y '(soup))) r)))
;; => ((split pea soup) (navy bean soup))

(defn teacupo
  [x]
  (conde
   ((== 'tea x))
   ((== 'cup x))
   (s# u#)))

(run* [x]
  (teacupo x))
;; => (tea cup)

(run* [r]
  (fresh [x y]
    (conde
     ((teacupo x) (== true y) s#)  ;; the "question" is the first goal of a line, the "answer" is the rest of the line
     ((== false x) (== true y))
     (s# u#))
    (== (cons x (cons y '())) r)))
;; => ((false true) (tea true) (cup true))

(run* [r]
  (fresh [x y z]
    (conde
     ((== y x) (fresh [x] (== z x)))
     ((fresh [x] (== y x)) (== z x))
     (s# u#))
    (== (cons y (cons z '())) r)))
;; => ((_0 _1) (_0 _1))

;; In the above example, it looks like both occurrences of _0 came from the same
;; variable. The example below proves this to be true.
(run* [r]
  (fresh [x y z]
    (conde
     ((== y x) (fresh [x] (== z x)))
     ((fresh [x] (== y x)) (== z x))
     (s# u#))
    (== false x)
    (== (cons y (cons z '())) r)))
;; => ((false _0) (_0 false))

;; Unification (`==`) is an expression whose value is a goal
(run* [q]
  (let [a (== true q)
        b (== false q)]
    b  ;; treat b as a goal
    ))
;; => (false)

;; It turns out that `==`, `fresh` and `conde` are ALL expressions, each of
;; whose value is a goal! Interesting...
(run* [q]
  (let [a (== true q)
        b (fresh [x]
            (== x q)
            (== false x))
        c (conde
           ((== true q) s#)
           (s# (== false q)))]
    b))
;; => (false)
