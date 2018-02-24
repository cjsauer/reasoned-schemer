(ns reasoned-schemer.core
  (:refer-clojure :exclude [== identity])
  (:require [clojure.core.logic
             :as l :refer [run* run s# u# == fresh conde firsto resto lcons lcons? llist conso emptyo nilo]]))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; 2. Teaching Old Toys New Tricks
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(let [x (fn [a] a)
      y 'c]
  (x y))
;; => c

;; Slightly shorter syntax than (cons x (cons y ...))
(run* [r]
  (fresh [y x]
    (== `(~x ~y) r)))
;; => ((_0 _1))

(run* [r]
  (fresh [v w]
    (let [x v
          y w]
      (== `(~x ~y) r))))
;; => ((_0 _1))

;; `car` in Scheme is `first` in Clojure
(first '(grape raisin pear))
;; => grape

(first '(a c o r n))
;; => a

(run* [r]
  (firsto '(a c o r n) r))
;; => (a)

(run* [q]
  (firsto '(a c o r n) 'a) ;; 'a is indeed the first of '(a c o r n), therefore success!
  (== true q))
;; => (true)

(run* [r]
  (fresh [x y]
    (firsto `(~r ~y) x)
    (== 'pear x)))
;; => (pear)

;; Implementation of `firsto`
(defn firsto*
  [p a]
  (fresh [d]
    (== (lcons a d) p)))

(run* [r]
  (fresh [x y]
    (firsto* `(~r ~y) x)
    (== 'pear x)))
;; => (pear)

(cons
 (first '(grape raisin pear))
 (first '((a) (b) (c))))
;; => (grape a)

(run* [r]
  (fresh [x y]
    (firsto '(grape raisin pear) x)
    (firsto '((a) (b) (c)) y)
    (== (lcons x y) r)))
;; => ((grape a))

(rest '(grape raisin pear))
;; => (raisin pear)

(first (rest '(a c o r n)))
;; => c

;; The process of transforming (first (rest ...)) into (rest l v) and (first v r) is
;; called "unnesting"
(run* [r]
  (fresh [v]
    (resto '(a c o r n) v)
    (firsto v r)))
;; => (c)

;; Implementation of `resto`
(defn resto*
  [p d]
  (fresh [a]
    (== (lcons a d) p)))

(run* [r]
  (fresh [v]
    (resto* '(a c o r n) v)
    (firsto* v r)))
;; => (c)

(cons
 (rest '(grape raisin pear))
 (first '((a) (b) (c))))
;; => ((raisin pear) a)

(run* [r]
  (fresh [x y]
    (resto '(grape raisin pear) x)
    (firsto '((a) (b) (c)) y)
    (== (lcons x y) r)))
;; => (((raisin pear) a))

(run* [q]
  (resto '(a c o r n) '(c o r n))  ;; '(c o r n) is indeed the rest of '(a c o r n), therefore success!
  (== true q))
;; => (true)

(run* [x]
  (resto '[c o r n] [x 'r 'n]))
;; => (o)

(run* [l]
  (fresh [x]
    (resto l '(c o r n))
    (firsto l x)
    (== 'a x)))
;; => ((a c o r n))

(run* [l]
  (conso '(a b c) '(d e) l))
;; => (((a b c) d e))

(run* [x]
  (conso x '(a b c) '(d a b c)))
;; => (d)

(run* [r]
  (fresh [x y z]
    (== ['e 'a 'd x] r)
    (conso y ['a z 'c] r)))
;; => ([e a d c])

(run* [x]
  (conso x ['a x 'c] ['d 'a x 'c]))
;; => (d)

(run* [l]
  (fresh [x]
    (== ['d 'a x 'c] l)
    (conso x ['a x 'c] l)))
;; => ([d a d c])

(run* [l]
  (fresh [x]
    (conso x ['a x 'c] l)
    (== ['d 'a x 'c] l)))
;; => ((d a d c))

(defn conso*
  [a d p]
  (== (lcons a d) p))

(run* [l]
  (fresh [x]
    (conso* x ['a x 'c] l)
    (== ['d 'a x 'c] l)))
;; => ((d a d c))

(run* [l]
  (fresh [d x y w s]
    (conso w '(a n s) s)
    (resto l s)
    (firsto l x)
    (== 'b x)
    (firsto s y)
    (== 'e y)))
;; => ((b e a n s))

(empty? '(grape raisin pear))
;; => false

(empty? '())
;; => true

(run* [q]
  (emptyo '(grape raisin pear))
  (== true q))
;; => ()

(run* [q]
  (emptyo '())
  (== true q))
;; => (true)

(run* [x]
  (emptyo x))
;; => (())

(defn emptyo*
  [x]
  (== x '()))

(run* [q]
  (emptyo* '(grape raisin pear))
  (== true q))
;; => ()

(run* [x]
  (emptyo* x))
;; => (())

(= 'pear 'plum)
;; => false

(= 'plum 'plum)
;; => true

(defn eqo
  [x y]
  (== x y))

(run* [q]
  (eqo 'pear 'plum)
  (== true q))
;; => ()

(run* [q]
  (eqo 'plum 'plum)
  (== true q))
;; => (true)

(lcons 'split 'pea)
;; => (split . pea)

(first '(pear))
;; => pear

(rest '(pear))
;; => ()

(defn pair?
  [x]
  (or (lcons? x) (and (coll? x) (seq x))))

(lcons '(split) 'pea)
;; => ((split) . pea)

(pair? (lcons '(split) 'pea))
;; => true

(pair? '())
;; => nil

(pair? 'pair)
;; => false

(pair? 'pear)
;; => false

(lcons 'pear '())
;; => (pear)

(pair? (lcons 'pear '()))
;; => (pear)

(run* [r]
  (fresh [x y]
    (== (lcons x (lcons y 'salad)) r)))
;; => ((_0 _1 . salad))

(defn pairo
  [p]
  (fresh [a d]
    (conso* a d p)))

(run* [q]
  (pairo (lcons q q))
  (== true q))
;; => (true)

(run* [q]
  (pairo '())  ;; the empty list is not a pair!
  (== true q))
;; => ()

(run* [q]
  (pairo 'pair)
  (== true q))
;; => ()

(run* [q]
  (pairo q))
;; => ((_0 . _1))

(run* [r]
  (pairo (lcons r 'pear)))
;; => (_0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; 3. Seeing Old Friends in New Ways
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; https://github.com/clojure/core.logic/wiki/Differences-from-The-Reasoned-Schemer
;; NOTE: In Clojure, it is more appropriate to use `seq?` than `list?` This is
;; because proper list-like things and pairs are not conflated in Clojure as
;; they are in Scheme.

(seq? '((a) (a b) c))
;; => true

(seq? '())
;; => true

(seq? 's)
;; => false

(llist 'd 'a 't 'e 's) ;; not a "proper" list
;; => (d a t e . s)
(seq? (llist 'd 'a 't 'e 's)) ;; and so is not a seq
;; => false

(defn listo
  [l]
  (conde
   ((emptyo l) s#)
   ((pairo l) (fresh [d]
                (resto l d)
                (listo d)))
   (s# u#)))

(run* [x]
  (listo (list 'a 'b x 'd)))
;; => (_0)

(run 1 [x]
  (listo (llist 'a 'b 'c x)))
;; => (())

(run 5 [x]
  (listo (llist 'a 'b 'c x)))
;; => (() (_0) (_0 _1) (_0 _1 _2) (_0 _1 _2 _3))

(defn lol?
  "list-of-lists?"
  [l]
  (cond
    (empty? l) true
    (seq? (first l)) (lol? (rest l))
    :else false))

(lol? '(() (1) (2)))
;; => true

(lol? '(() 1 2))
;; => false

;; Switching to using vectors as the `conde` clauses for readability here...
(defn lolo
  [l]
  (conde
   [(emptyo l) s#]
   [(fresh [a]
      (firsto l a)
      (listo a))
    (fresh [b]
      (resto l b)
      (lolo b))]
   [s# u#]))

(run 1 [l]
  (lolo l))
;; => (())

(run* [q]
  (fresh [x y]
    (lolo (list '(a b) (list x 'c) (list 'd y)))
    (== true q)))
;; => (true)

(run 1 [q]
  (fresh [x]
    (lolo (llist '(a b) x))
    (== true q)))
;; => (true)

(run 1 [x]
  (lolo (llist '(a b) '(c d) x)))
;; => (())

;; Borrowed from:
;; https://github.com/candera/reasoned-schemer/blob/master/src/reasoned_schemer/chapter3.clj
;;
;; TRS has this as
;; (()
;;  (())
;;  (() ())
;;  (() () ())
;;  (() () () ())
;;
;; The reason for the difference is that conde in the book is a
;; depth-first search where conde in core.logic is an interleaving
;; one.

(run 5 [x]
  (lolo (llist '(a b) '(c d) x)))
;; => (()
;;     (())
;;     ((_0))
;;     (() ())
;;     ((_0 _1)))

(defn twinso
  [s]
  (fresh [x y]
    (conso x y s)
    (conso x '() y)))

(run* [q]
  (twinso '(tofu tofu))
  (== true q))
;; => (true)

(run* [z]
  (twinso (list z 'tofu)))
;; => (tofu)

;; Implementation without `conso`
(defn twinso*
  [s]
  (fresh [x y]
    (== s (list x x))))

(run* [z]
  (twinso* (list z 'tofu)))
;; => (tofu)

(defn loto
  [l]
  (conde
   [(emptyo l) s#]
   [(fresh [a]
      (firsto l a)
      (twinso a))
    (fresh [d]
      (resto l d)
      (loto d))]
   [s# u#]))

(run 1 [z]
  (loto (llist '(g g) z)))
;; => (())

(run 5 [z]
  (loto (llist '(g g) z)))
;; => (()
;;    ((_0 _0))
;;    ((_0 _0) (_1 _1))
;;    ((_0 _0) (_1 _1) (_2 _2))
;;    ((_0 _0) (_1 _1) (_2 _2) (_3 _3)))

(run 5 [r]
  (fresh [w x y z]
    (loto (llist '(g g) (list 'e w) (list x y) z))
    (== (list w (list x y) z) r)))
;; => ((e (_0 _0) ())
;;     (e (_0 _0) ((_1 _1)))
;;     (e (_0 _0) ((_1 _1) (_2 _2)))
;;     (e (_0 _0) ((_1 _1) (_2 _2) (_3 _3)))
;;     (e (_0 _0) ((_1 _1) (_2 _2) (_3 _3) (_4 _4))))

(run 3 [out]
  (fresh [w x y z]
    (== (llist '(g g) (list 'e w) (list x y) z) out)
    (loto out)))
;; => (((g g) (e e) (_0 _0))
;;     ((g g) (e e) (_0 _0) (_1 _1))
;;     ((g g) (e e) (_0 _0) (_1 _1) (_2 _2)))

(defn listofo
  [predo l]
  (conde
   [(emptyo l) s#]
   [(fresh [a]
      (firsto l a)
      (predo a))
    (fresh [d]
      (resto l d)
      (listofo predo d))]
   [s# u#]))

(run 3 [out]
  (fresh [w x y z]
    (== (llist '(g g) (list 'e w) (list x y) z) out)
    (listofo twinso out)))
;; => (((g g) (e e) (_0 _0))
;;     ((g g) (e e) (_0 _0) (_1 _1))
;;     ((g g) (e e) (_0 _0) (_1 _1) (_2 _2)))

;; redefine `loto` using `listofo`
(defn loto
  [l]
  (listofo twinso l))

(run 1 [z]
  (loto (llist '(g g) z)))
;; => (())

(defn eq-first?
  [l x]
  (= x (first l)))

(defn member?
  [x l]
  (cond
    (empty? l) false
    (eq-first? l x) true
    :else (member? x (rest l))))

(member? 'olive '(virgin olive oil))
;; => true

(defn eq-firsto
  [l x]
  (firsto l x))

(defn membero
  [x l]
  (conde
   ;; [(emptyo l) u#]    <-- `conde` lines guaranteed to fail are unnecessary
   [(eq-firsto l x) s#]
   [s# (fresh [d]
         (resto l d)
         (membero x d))]))

(run* [q]
  (membero 'olive '(virgin olive oil))
  (== true q))
;; => (true)

(run 1 [y]
  (membero y '(hummus with pita)))
;; => (hummus)

(run 1 [y]
  (membero y '(with pita)))
;; => (with)

(run 1 [y]
  (membero y '(pita)))
;; => (pita)

(run* [y]
  (membero y '()))
;; => ()

(defn identity
  [l]
  (run* [y]
    (membero y l)))

(run* [x]
  (membero 'e (list 'pasta x 'fagioli)))
;; => (e)

;; Recursion succeeds _before_ it gets to variable x
(run 1 [x]
  (membero 'e (list 'pasta 'e x 'fagioli)))
;; => (_0)

;; Recursion succeeds _when_ it gets to variable x
(run 1 [x]
  (membero 'e (list 'pasta x 'e 'fagioli)))
;; => (e)

(run* [r]
  (fresh [x y]
    (membero 'e (list 'pasta x 'fagioli y))
    (== (list x y) r)))
;; => ((e _0) (_0 e))

(run 1 [l]
  (membero 'tofu l))
;; => ((tofu . _0))

(run 5 [l]
  (membero 'tofu l))
;; => ((tofu . _0)
;;     (_0 tofu . _1)
;;     (_0 _1 tofu . _2)
;;     (_0 _1 _2 tofu . _3)
;;     (_0 _1 _2 _3 tofu . _4))

(defn pmembero
  [x l]
  (conde
   [(emptyo l) u#]
   [(eq-firsto l x) (resto l '())]
   [s# (fresh [d]
         (resto l d)
         (pmembero x d))]))

(run 5 [l]
  (pmembero 'tofo l))
;; => ((tofo)
;;     (_0 tofo)
;;     (_0 _1 tofo)
;;     (_0 _1 _2 tofo)
;;     (_0 _1 _2 _3 tofo))

;; result is not (true true), first tofu is not at end of list
(run* [q]
  (pmembero 'tofu '(a b tofu d tofu))
  (== true q))
;; => (true)

(defn pmembero*
  [x l]
  (conde
   [(emptyo l) u#]
   [(eq-firsto l x) (resto l '())] ;; this line contributes 1 value
   [(eq-firsto l x) s#]            ;; this line contributes 2 values
   [s# (fresh [d]
         (resto l d)
         (pmembero* x d))]))

(run* [q]
  (pmembero* 'tofu '(a b tofu d tofu))
  (== true q))
;; => (true true true)

(defn pmembero**
  [x l]
  (conde
   ;; [(emptyo l) u#]               ;; again, lines that always fail can be removed
   [(eq-firsto l x) (resto l '())]
   [(eq-firsto l x) (fresh [a d]
                      (resto l (lcons a d)))]  ;; check to make sure `rest` of l is not empty
   [s# (fresh [d]
         (resto l d)
         (pmembero** x d))]))

(run* [q]
  (pmembero** 'tofu '(a b tofu d tofu))
  (== true q))
;; => (true true)

(run 12 [l]
  (pmembero** 'tofu l))
;; => ((tofu)
;;     (tofu _0 . _1)
;;     (_0 tofu)
;;     (_0 tofu _1 . _2)
;;     (_0 _1 tofu)
;;     (_0 _1 tofu _2 . _3)
;;     (_0 _1 _2 tofu)
;;     (_0 _1 _2 tofu _3 . _4)
;;     (_0 _1 _2 _3 tofu)
;;     (_0 _1 _2 _3 tofu _4 . _5)
;;     (_0 _1 _2 _3 _4 tofu)
;;     (_0 _1 _2 _3 _4 tofu _5 . _6))

(defn pmembero**-rev
  [x l]
  (conde
   ;; swap these two `conde` lines, results in swapped output
   [(eq-firsto l x) (fresh [a d]
                      (resto l (lcons a d)))]
   [(eq-firsto l x) (resto l '())]
   [s# (fresh [d]
         (resto l d)
         (pmembero**-rev x d))]))

;; Compare these results with the example above
(run 12 [l]
  (pmembero**-rev 'tofu l))
;; => ((tofu _0 . _1)
;;     (tofu)
;;     (_0 tofu _1 . _2)
;;     (_0 tofu)
;;     (_0 _1 tofu _2 . _3)
;;     (_0 _1 tofu)
;;     (_0 _1 _2 tofu _3 . _4)
;;     (_0 _1 _2 tofu)
;;     (_0 _1 _2 _3 tofu _4 . _5)
;;     (_0 _1 _2 _3 tofu)
;;     (_0 _1 _2 _3 _4 tofu _5 . _6)
;;     (_0 _1 _2 _3 _4 tofu))

(defn first-value
  [l]
  (run 1 [y]
    (membero y l)))

(first-value '(pasta e fagioli))
;; => (pasta)

;; This doesn't work in core.logic. `conde` in core.logic is actually the book's
;; `condi`, and so order of results will vary
(defn memberrevo
  [x l]
  (conde
   [s# (fresh [d]
         (resto l d)
         (memberrevo x d))]
   [s# (eq-firsto l x)]))

(run* [x]
  (memberrevo x '(pasta e fagioli)))
;; => (pasta e fagioli)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; 4. Members Only
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn mem
  [x l]
  (cond
   (empty? l) false
   (eq-first? l x) l
   :else (mem x (rest l))))

(mem 'tofu '(a b tofu d peas e))
;; => (tofu d peas e)

(mem 'tofu '(a b peas d peas e))
;; => false

(run* [out]
  (== (mem 'tofu '(a b tofu d peas e)) out))
;; => ((tofu d peas e))

(mem 'peas
     (mem 'tofu '(a b tofu d peas e)))
;; => (peas e)

(mem 'tofu
     (mem 'tofu '(a b tofu d tofu e)))
;; => (tofu d tofu e)

(mem 'tofu
     (rest (mem 'tofu '(a b tofu d tofu e))))
;; => (tofu e)

(defn memo
  [x l out]
  (conde
   [(eq-firsto l x) (== l out)]
   [s# (fresh [d]
         (resto l d)
         (memo x d out))]))

(run 1 [out]
  (memo 'tofu '(a b tofu d tofu e) out))
;; => ((tofu d tofu e))

(run 1 [out]
  (fresh [x]
    (memo 'tofu (list 'a 'b x 'd 'tofu 'e) out)))
;; => ((tofu d tofu e))

(run* [r]
  (memo r
        '(a b tofu d tofu e)
        '(tofu d tofu e)))
;; => (tofu)

(run* [q]
  (memo 'tofu '(tofu e) '(tofu e))
  (== true q))
;; => (true)

(run* [q]
  (memo 'tofu '(tofu e) '(tofu))
  (== true q))
;; => ()

(run* [x]
  (memo 'tofu '(tofu e) (list x 'e)))
;; => (tofu)

(run* [x]
  (memo 'tofu '(tofu e) (list 'peas x)))
;; => ()

(run* [out]
  (fresh [x]
    (memo 'tofu (list 'a 'b x 'd 'tofu 'e) out)))
;; => ((tofu d tofu e) (tofu e))

(run 12 [z]
  (fresh [u]
    (memo 'tofu (llist 'a 'b 'tofu 'd 'tofu 'e z) u)))
;; => (_0
;;     _0
;;     (tofu . _0)
;;     (_0 tofu . _1)
;;     (_0 _1 tofu . _2)
;;     (_0 _1 _2 tofu . _3)
;;     (_0 _1 _2 _3 tofu . _4)
;;     (_0 _1 _2 _3 _4 tofu . _5)
;;     (_0 _1 _2 _3 _4 _5 tofu . _6)
;;     (_0 _1 _2 _3 _4 _5 _6 tofu . _7)
;;     (_0 _1 _2 _3 _4 _5 _6 _7 tofu . _8)
;;     (_0 _1 _2 _3 _4 _5 _6 _7 _8 tofu . _9))

(defn rember
  [x l]
  (cond
    (empty? l) '()
    (eq-first? l x) (rest l)
    :else (cons (first l)
                (rember x (rest l)))))

(rember 'peas '(a b peas d peas e))
;; => (a b d peas e)

(rember 'peas
        (rember 'peas '(a b peas d peas e)))
;; => (a b d e)

(defn rembero
  [x l out]
  (conde
   [(emptyo l) (== out '())]
   [(eq-firsto l x) (resto l out)]
   [s# (fresh [a d res]
         (conso a d l)
         (rembero x d res)
         (conso a res out))]))

(run 1 [out]
  (fresh [y]
    (rembero 'peas (list 'a 'b y 'd 'peas 'e) out)))
;; => ((a b d peas e))

(run* [out]
  (fresh [y z]
    (rembero y (list 'a 'b y 'd z 'e) out)))
;; => ((b a d _0 e)
;;     (a b d _0 e)
;;     (a b d _0 e)
;;     (a b d _0 e)
;;     (a b _0 d e)
;;     (a b e d _0)
;;     (a b _0 d _1 e))

(run* [r]
  (fresh [y z]
    (rembero y (list y 'd z 'e) (list y 'd 'e))
    (== (list y z) r)))
;; => ((d d)
;;     (d d)
;;     (_0 _0)
;;     (e e))

(rember 'd '(d d d e))
;; => (d d e)

(rember 'a '(a d a e))
;; => (d a e)

(rember 'e '(e d e e))
;; => (d e e)

;; wtf...
;; these values are producing non-solutions to `rembero`...
;; skipping to `surpriseo` out of confusion...

(defn surpriseo
  [s]
  (rembero s '(a b c) '(a b c)))

(run* [r]
  (== 'd r)
  (surpriseo r))
;; => (d)

(run* [r]
  (surpriseo r))
;; => (_0)

(run* [r]
  (surpriseo r)
  (== r 'b))
;; => (b)

;; Seriously tho...dafuq is going on here
(run* [r]
  (== r 'b)
  (surpriseo r))
;; => (b)
