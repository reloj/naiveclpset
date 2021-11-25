(ns naiveclpset.main
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all]
            [clojure.core.logic.protocols :refer :all]
            [clojure.math.combinatorics :refer :all]))

(extend-protocol IWalkTerm
  clojure.lang.IPersistentSet
  (walk-term [v f] (with-meta (set (walk-term (seq v) f)) (meta v))))

(extend-protocol IUnifyTerms
  clojure.lang.IPersistentSet
  (unify-terms [u v s]
    (when (set? v)
      (let [u (seq u)
            v (seq v)]
        (reduce #(mplus % (-inc %2))
                (for [p (permutations u)] (unify s p v)))))))

(comment
  (run* [q] (== q []))
  (run* [q] (== q #{}))
  (run* [q] (== q [1 2 3]))
  (run* [q] (== q #{1 2 3}))
  (run* [q] (== [1 q 3] [1 2 3]))
  (run* [q] (== #{1 q 3} #{1 2 3}))
  (run* [q] (== #{1 3 q} #{1 2 3}))
  (run* [q] (== #{1 q 3} #{1 2 3}))
  (run* [q] (== #{3 1 q} #{1 2 3}))
  (run* [q] (fresh [a1 a2 a3] (== #{a1 a2 a3} #{1 2 3}) (== q [a1 a2 a3])))
  (run* [q] (== #{1 2 [3 q]} #{1 2 [3 4]}))
  (run* [q] (== #{1 2 #{3 q}} #{1 2 #{3 4}})) ; fails!
  (run* [q] (== #{ #{ #{q} :bar} :baz}  #{:baz #{:bar #{:foo}}}))
)
