(ns reasoned-schemer.core2e
  (:refer-clojure :exclude [== identity])
  (:require [clojure.core.logic
             :as l :refer [run* run s# u# == fresh conde firsto resto lcons
                           lcons? llist conso emptyo nilo defne]]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Playthings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(run* [q]
  u#)
;; => ()

(run* [q]
  (== 'pea 'pod))
;; => ()

(run* [q]
  (== q 'pea))
;; => (pea)

(run* [q]
  (== 'pea q))
;; => (pea)

;; q remains fresh
(run* [q]
  s#)
;; => (_0)

;; q remains fresh
(run* [q]
  (== 'pea 'pea))
;; => (_0)

;; q remains fresh
(run* [q]
  (== q q))
;; => (_0)

;; unused variable does not change the value associated with any other variable
(run* [q]
  (fresh [x]
    (== q 'pea)))
;; => (pea)

;; q remains fresh
(run* [q]
  (fresh [x]
    (== x 'pea)))
;; => (_0)

;; x remains fresh
(run* [q]
  (fresh [x]
    (== (cons x '()) q)))
;; => ((_0))

;; equivalent to above but more concise
(run* [q]
  (fresh [x]
    (== `(~x) q)))
;; => ((_0))

;; fusing q and x
(run* [q]
  (fresh [x]
    (== q x)))
;; => (_0)

(run* [q]
  (== '(((pea)) pod) `(((~'pea)) ~q)))
;; => (pod)

(run* [q]
  (fresh [x]
    (== `(((~q)) ~'pod) `(((~x)) ~'pod))))
;; => (_0)

(run* [q]
  (fresh [x]
    (== `(((~q)) ~x) `(((~x)) ~'pod))))
;; => (pod)

(run* [q]
  (fresh [x]
    (== `(~x ~x) q)))
;; => ((_0 _0))

(run* [q]
  (fresh [x y]
    (== `(~q ~y) `((~x ~y) ~x))))
;; => ((_0 _0))

;; every variable introduced by fresh or run* is initially different from every
;; other variable
(run* [q]
  (fresh [x y]
    (== q `(~x ~y))))
;; => ((_0 _1))

;; (pea) is not the same as pea
(run* [q]
  (== '(pea) 'pea))
;; => ()

;; (== `(~x) x) will never succeed. x cannot be equal to a list in which x occurs.
;;
;; A variable x occurs in y when x (or any variable fused with x) appears in the value
;; associated with y.
;; A variable x occurs in a list l when x (or any variable fused with x) is an element
;; of l, or when x occurs in an element of l.
;;
;; e.g. x "occurs" in:
;; `(pea (~x) pod)
;;
;; therefore (== v x) succeeds and associates v with x, unless x occurs in v
;; -----


;; the book uses conj2, which is the same as core.logic's run* given two goals.
(run* [q]
  s#
  s#)
;; => (_0)

(run* [q]
  s#
  (== 'corn q))
;; => (corn)

(run* [q]
  u#
  (== 'corn q))
;; => ()

(run* [q]
  (== 'corn q)
  (== 'meal q))
;; => ()

(run* [q]
  (== 'corn q)
  (== 'corn q))
;; => (corn)

;; core.logic does not have either conj2 or disj2, as defined in the book.
;; instead, conde is defined as a disj2 containing conj2's.
;; it can be read as:
;; (run* [q]
;;   (OR
;;     [goal1 AND goal2 AND ...]
;;     ...))
;; where OR is conde
;; https://github.com/clojure/core.logic/wiki/A-Core.logic-Primer

(run* [q]
  (conde   ;; "disj2"
   [u#]    ;; g1
   [u#]    ;; g2
   ))
;; => ()
;; because the goal (disj2 g1 g2) fails if both g1 and g2 fail

(run* [q]
  (conde           ;; "disj2"
   [u#]            ;; g1
   [(== 'olive q)] ;; g2
   ))
;; => (olive)
;; because the goal (disj2 g1 g2) succeeds if either g1 or g2 succeeds

(run* [q]
  (conde           ;; "disj2"
   [(== 'olive q)] ;; g2
   [u#]            ;; g1
   ))
;; => (olive)
;; because the goal (disj2 g1 g2) succeeds if either g1 or g2 succeeds

(run* [q]
  (conde
   [(== 'olive q)]
   [(== 'oil q)]))
;; => (olive oil)
;; Both goals contribute values. (== 'olive q) succeeds, and olive is the first
;; value associated with q.
;; (== 'oil q) succeeds, and oil is the second value associated with q.

(run* [q]
  (fresh [x y]
    (conde
     [(== `(~x ~y) q)]
     [(== `(~y ~x) q)]
     )))
;; => ((_0 _1) (_0 _1))
;; Notice that disj2 (conde) creates two completely separate "paths",
;; and so x is reified as _0 in the first path, and _1 in the second.
;; Each value produced by a run* expression is reified independently.
;; The numbering of reified variables begins again at 0 within each
;; reified value.

;; A
(run* [q]
  (conde
   [(== q 'olive)]
   [(== q 'oil)]))
;; => (olive oil)

;; B
(run* [q]
  (conde
   [(== q 'oil)]
   [(== q 'olive)]))
;; => (oil olive)
;; We consider A and B to be the same, because with disj (conde), order
;; does NOT matter.

(run* [q]
  (conde
   [(== q 'olive) u#]
   [(== q 'oil)]))
;; => (oil)
;; The first "path" is unsuccessful

(run* [q]
  (conde
   [(== q 'olive) s#]
   [(== q 'oil)]))
;; => (olive oil)
;; This time, the first "path" is successful, so q unifies with 'olive

(run* [q]
  (conde
   [(== q 'oil)]
   [(== q 'olive) s#]))
;; => (oil olive)
;; Again, order does not matter

(run* [q]
  (conde
   [(== 'virgin q) u#]
   [(conde
     [(== 'olive q)]
     [(conde
       [s#]
       [(== 'oil q)])])]))
;; => (olive _0 oil)
;; How do we end up with _0?
;; Through the s# in the innermost disj (conde), which succeeds without
;; associating a value with q.

(run* [r]
  (fresh [x y]
    (== 'split x)
    (== 'pea y)
    (== r `(~x ~y))))
;; => ((split pea))

;; Does this produce the same thing?
(run* [r x y]
  (== 'split x)
  (== 'pea y)
  (== r `(~x ~y)))
;; => ([(split pea) split pea])
;; Nope.
;; Can it be made to produce the same thing?

(run* [x y]
  (== 'split x)
  (== 'pea y))
;; => ([split pea])
;; Yep!

(run* [x y]
  (conde
   [(== 'split x) (== 'pea y)]
   [(== 'red x) (== 'bean y)]))
;; => ([split pea] [red bean])

(run* [r]
  (fresh [x y]  ;; fresh can also behave like conj e.g. (conj g1 (conj g2 (conj g3 ...)))
    (conde                          ;; g1
     [(== 'split x) (== 'pea y)]
     [(== 'red x) (== 'bean y)])
    (== r `(~x ~y ~'soup))))        ;; g2
;; => ((split pea soup) (red bean soup))

(run* [x y z]
  (conde
   [(== 'split x) (== 'pea y)]
   [(== 'red x) (== 'bean y)])
  (== 'soup z))
;; => ([split pea soup] [red bean soup])
;; A bit more concision can be had by moving fresh variables up into the run* expression.
;; -------


;; This is a relation
(defn teacupo
  [t]
  (conde
   [(== 'tea t)]
   [(== 'cup t)]))
;; A relation is a function that, when given arguments, produces a goal.

;; core.logic shorthand for relations supporting pattern matching
(defne teacupo
  [t]
  (['tea])
  (['cup]))

(run* [q]
  (teacupo q))
;; => (tea cup)

(run* [x y]
  (conde
   [(teacupo x) (== y true)]
   [(== x false) (== y true)]))
;; => ([false true] [tea true] [cup true])
;; (remember that order of values does not matter)

(run* [x y]
  (teacupo x)
  (teacupo y))
;; => ([tea tea] [tea cup] [cup tea] [cup cup])

(run* [x y]
  (teacupo x)   ;; associates x with 'tea and 'cup.
  (teacupo x))  ;; already has the correct associations, so succeeds without associating anything
;; => ([tea _0] [cup _0])
;; y remains fresh

(run* [x y]
  (conde
   [(teacupo x) (teacupo x)]
   [(== false x) (teacupo y)]))
;; => ([false tea] [false cup] [tea _0] [cup _0])

(run* [x y]
  (conde
   [(fresh [z]
      (== z 'lentil))]
   [(== x y)]))
;; => ([_0 _0] [_0 _1])
;; First "path": x and y remain fresh, z is unified to 'lentil, but is not reified in the result
;; Second "path": both x and y remain fresh, but are fused

(run* [x y]
  (conde
   [(== 'split x) (== 'pea y)]
   [(== 'red x) (== 'bean y)]
   [(== 'green x) (== 'lentil y)]
   ))
;; => ([split pea] [red bean] [green lentil])
;; conde can take any number of conjunctions
;; the "e" in conde stands for "every", because every successful line contributes one or more values.
;; --------------------------------------------------





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Teaching Old Toys New Tricks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(first '(grape raisin pear))
;; => grape

(first '(a c o r n))
;; => a

(run* [q]
  (firsto '(a c o r n) q))
;; => (a)

(run* [q]
  (firsto '(a c o r n) 'a))
;; => (_0)
;; goal succeeds, while q remains fresh

(run* [q]
  (firsto '(a c o r n) 'nope))
;; => ()

(run* [r]
  (fresh [x y]
    (firsto `(~r ~y) x)
    (== 'pear x)))
;; => (pear)
;; The fresh variable r is fused with x, because r is the first of `(~r ~y),
;; then 'pear is associated with x, which in turn associates r with 'pear

;; Example definition of firsto
(defn firsto*
  [l a]
  (fresh [d]
    (conso a d l)))
;; Note that while first accepts 1 arg, firsto* accepts 2

(run* [r]
  (firsto* '(a c o r n) r))
;; => (a)

(run* [r]
  (fresh [x y]
    (firsto '(grape raisin pear) x)
    (firsto '((a) (b) (c)) y)
    (== (lcons x y) r)))
;; => ((grape a))

(rest '(grape raisin pear))
;; => (raisin pear)

(first (rest (rest '(a c o r n))))
;; => o

(run* [r]
  (fresh [v w]
    (resto '(a c o r n) v)
    (resto v w)
    (firsto w r)))
;; => (o)

;; Example implementation of resto
(defn resto*
  [l d]
  (fresh [a]
    (conso a d l)))

(run* [r]
  (resto* '(a c o r n) r))
;; => ((c o r n))

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
  (resto '(a c o r n) '(c o r n)))
;; => (_0)
;; Because goal succeeds, but q remains fresh

(run* [q]
  (resto '(c o r n) `(~q ~'r ~'n)))
;; => (o)

(run* [l]
  (fresh [x]
    (resto l '(c o r n))  ;; the rest of l is '(c o r n)
    (firsto l x)          ;; the first of l is x
    (== x 'a)))           ;; x is 'a
;; => ((a c o r n))

(run* [l]
  (conso '(a b c) '(d e) l))
;; => (((a b c) d e))

(run* [x]
  (conso x '(a b c) '(d a b c)))
;; => (d)

(run* [r]
  (fresh [x y z]
    (== (llist 'e 'a 'd x) r)
    (conso y (llist 'a z 'c) r)))
;; => ((e a d . c))

(run* [x]
  (conso x (llist 'a x 'c) (llist 'd 'a x 'c)))
;; => (d)

(run* [l]
  (fresh [x]
    (== (llist 'd 'a x 'c) l)
    (conso x (llist 'a x 'c) l)))
;; => ((d a d . c))

(run* [l]
  (fresh [x]
    (conso x (llist 'a x 'c) l)
    (== (llist 'd 'a x 'c) l)))
;; => ((d a d . c))
;; Order does not matter in this case

;; Example implementation of conso
(defn conso*
  [a d l]
  (conde
   [(firsto l a) (resto l d)]))

(run* [x]
  (conso* x '(a b c) '(d a b c)))
;; => (d)

;; Another example implementation
(defn conso**
  [a d l]
  (== (lcons a d) l))

(run* [x]
  (conso** x '(a b c) '(d a b c)))
;; => (d)

(run* [l]
  (fresh [d t x y w]
    (conso w '(n u s) t)
    (resto l t)
    (firsto l x)
    (== 'b x)
    (resto l d)
    (firsto d y)
    (== 'o y)))
;; => ((b o n u s))

(empty? '(grape raisin pear))
;; => false

(empty? '())
;; => true

(run* [q]
  (emptyo '(grape raisin pear)))
;; => ()
;; Goal fails, because '(grape raisin pear) is not empty

(run* [q]
  (emptyo '()))
;; => (_0)
;; Goal succeeds, while q remains fresh

(run* [x]
  (emptyo x))
;; => (())
;; Because the only way emptyo succeeds is if x is the empty list '()

;; Example implementation of emptyo
(defn emptyo*
  [l]
  (== l '()))

(run* [x]
  (emptyo* x))
;; => (())

(lcons? (lcons 'split 'pea))
;; => true

(lcons? (lcons '(split) 'pea))
;; => true

(lcons? '())
;; => false

(defn pair?
  [x]
  (or (lcons? x) (and (coll? x) (seq x))))

(defn pairo
  [p]
  (fresh [a d]
    (conso a d p)))

(run* [q]
  (pairo (lcons q q)))
;; => (_0)
;; lcons creates a pair of the same fresh variable, but we are only interested
;; in q here, not the pair.

(run* [q]
  (pairo '()))
;; => ()

(run* [q]
  (pairo 'pear))
;; => ()

(run* [x]
  (pairo x))
;; => ((_0 . _1))

(run* [r]
  (pairo (lcons r '())))
;; => (_0)

;; a "singleton" is defined as a list of a single value
;; Are these examples singletons:
;; '(tofu)    YES
;; '((tofu))  YES
;; 'tofu      NO
;; '(e tofu)  NO
;; '()        NO
;; (e . tofu) NO

(defn singleton?
  [l]
  (cond
    (pair? l) (empty? (rest l))
    :else false))

(singleton? '())
;; => false

(singleton? (lcons 'pea nil))
;; => true

(singleton? '(sauerkraut))
;; => true

(defn singletono
  [l]
  (fresh [d]
    (resto l d)
    (emptyo d)))
;; --------------------------------------------------




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Seeing Old Friends in New Ways
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; list? is unnecessary to implement in Clojure, as seq? is much more appropriate.
;; This is because list-like things and pairs are not conflated in Clojure as they
;; are in Scheme.

(seq? '())
;; => true

(seq? 's)
;; => false

(seq? (llist 'd 'a 't 'e 's))
;; => false
;; ('d 'a 't 'e . 's) is not a "proper" list

(defn listo
  [l]
  (conde
   [(emptyo l)]
   [(fresh [d]
      (resto l d)
      (listo d))]))

(run* [x]
  (listo (list 'a 'b x 'd)))
;; => (_0)

;; (run* [x]
;;   (listo (llist 'a 'b 'c x)))
;; This expression has an unbounded number of possible values for x,
;; and so we say it has "no value".
;; We can use run 1 to get a list of only the first value:

(run 1 [x]
  (listo (llist 'a 'b 'c x)))
;; => (())
;; Looking back at the definition for listo, when listo reaches the end of (llist 'a 'b 'c x),
;; (emptyo x) succeeds and associates x with the empty list '().

;; We can get more values:
(run 5 [x]
  (listo (llist 'a 'b 'c x)))
;; => (()
;;     (_0)
;;     (_0 _1)
;;     (_0 _1 _2)
;;     (_0 _1 _2 _3))

(defn lol?
  "List of lists?"
  [l]
  (cond
    (empty? l) true
    (seq? (first l)) (lol? (rest l))
    :else false))

(lol? '((a) (b)))
;; => true

(lol? '(a b c))
;; => false

(defn lolo
  [l]
  (conde
   [(emptyo l)]
   [(fresh [a]
      (firsto l a)
      (listo a))
    (fresh [d]
      (resto l d)
      (lolo d))]))

(run* [q]
  (fresh [x y]
    (lolo (list '(a b)
                (list x 'c)
                (list 'd y)))))
;; => (_0)
;; Goal succeeds, and q remains fresh

(run 1 [l]
  (lolo l))
;; => (())
;; l is fresh, (emptyo l) succeeds and associates l with '()

(run 1 [q]
  (fresh [x]
    (lolo (llist '(a b) x))))
;; => (_0)

(run 1 [x]
  (lolo (llist '(a b)
               '(c d)
               x)))
;; => (())

(run 5 [x]
  (lolo (llist '(a b)
               '(c d)
               x)))
;; => (()
;;     (())
;;     ((_0))
;;     (() ())
;;     ((_0 _1)))

;; Side note: list and llist seem to behave differently when it comes to the order
;; in which variables are reified in the result. I imagine we'll learn why this is so
;; once we "open the hood".
