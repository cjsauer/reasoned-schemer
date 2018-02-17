(ns reasoned-schemer.core
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :as l :refer [run* s# u# == fresh]]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; 1. Playthings
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

false
true

;; a goal that succeeds
;; "succeed"
s#

;; a goal that fails; it is unsuccessful
;; "fail"
u#

(run* [q]
  u#)
;; => ()

(run* [q]
  (== true q))
;; => (true)

(run* [q]
  u#
  (== true q))
;; => ()

(run* [q]
  s#
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

(run* [x]
  (let [x true]
    (== x false)))
;; => ()

;; Both `q` and `x` are "fresh" here
(run* [q]
  (fresh [x]
    (== x true)
    (== true q)))
;; => (true)
