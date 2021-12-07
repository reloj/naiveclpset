(ns naiveclpset.main
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all]
            [clojure.core.logic.protocols :refer :all]
            [clojure.math.combinatorics :refer :all]))

(extend-protocol IWalkTerm
  clojure.lang.IPersistentSet
  (walk-term [v f] (with-meta (set (walk-term (seq v) f)) (meta v))))

(extend-protocol IUnifyTerms
  clojure.lang.IPersistentMap
  (unify-terms [u v s] ; adapted from the original definition...
    (cond
      (instance? clojure.core.logic.protocols.IUnifyWithRecord v)
      (unify-with-record v u s)

      (map? v)
      (unify-with-map* u v s)

      (set? v) ; ...to add the option to unify with a set...
      (unify-terms v u s) ; ...which is handled below for the symmetric case

      :else nil))

  clojure.lang.IPersistentSet
  (unify-terms [u v s]
    (cond
      (map? v)
      (unify-terms u (set v) s) ; a map is just a set of key-value vectors

      (set? v)
      (let [u (seq u)
            v (seq v)]
        (reduce #(mplus % (-inc %2))
                (for [p (permutations u)] (unify s p v))))

      :else nil)))

(comment
  ;; original author tests
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

  ;; a set of kv vectors should unify with a map
  (run* [q] (== #{[:a 1]} #{[:a q]}))
  (run* [q] (== #{[:a 1]} {:a q}))
  (run* [q] (== {:a 1} #{[:a q]}))
)
