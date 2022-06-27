(ns naiveclpset.main
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all]
            [clojure.core.logic.protocols :refer :all]
            [clojure.math.combinatorics :refer :all]))

(extend-protocol IWalkTerm
  clojure.lang.IPersistentMap
  (walk-term [v f] (with-meta (hash-map (flatten (walk-term (seq v) f))) (meta v)))

  clojure.lang.IPersistentSet
  (walk-term [v f] (with-meta (set (walk-term (seq v) f)) (meta v))))

(extend-protocol IUnifyTerms
  clojure.lang.IPersistentMap
  (unify-terms [u v s] ; copied from the original definition...
    (cond
      (instance? clojure.core.logic.protocols.IUnifyWithRecord v)
      (unify-with-record v u s)

      (map? v)
      (unify-with-map* u v s)

      (set? v) ; ...to add the option to unify with a set...
      (unify-terms v u s) ; ...which is handled below for the symmetric case

      (lcons? v)
      (unify-terms v u s) ; ...idem for lcons

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

      (lcons? v)
      (unify-terms v u s) ; lcons unification done on the symmetric case

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

  ;; Note that sets are "unordered", they should not unify with something with order! They aren't really the same if only one has an order, right? Use permuteo otherwise!
  (run* [q] (== [1 2 3] #{3 2 1}))
  (run* [q] (permuteo [1 2 3] #{3 2 1}))

  ;; a set of kv vectors should unify with a map
  (run* [q] (== #{[:a 1]} #{[:a q]}))
  (run* [q] (== #{[:a 1]} {:a q}))
  (run* [q] (== {:a 1} #{[:a q]}))
)

(comment
(extend-protocol IUnifyTerms ;; cant extend it; see https://stackoverflow.com/questions/3589569/whats-the-rationale-behind-closed-records-in-clojure
  clojure.core.logic.LCons
  (unify-terms [u v s] ;; copied from the original definition...
    (cond
      (sequential? v)
      (loop [u u v (seq v) s s]
        (if-not (nil? v)
          (if (lcons? u)
            (if-let [s (unify s (lfirst u) (first v))]
              (recur (lnext u) (next v) s)
              nil)
            (unify s u v))
          (if (lvar? u)
            (if-let [s (unify s u '())]
              s
              (unify s u nil))
            nil)))

      ;; ...to add this condition so conso unifies with maps and sets
      (or (map? v)(set? v))
      (reduce #(mplus % (-inc %2))
              (for [p (permutations v)] (unify s u p)))

      (lcons? v)
      (loop [u u v v s s]
        (if (lvar? u)
          (unify s u v)
          (cond
            (lvar? v) (unify s v u)
            (and (lcons? u) (lcons? v))
            (if-let [s (unify s (lfirst u) (lfirst v))]
              (recur (lnext u) (lnext v) s)
              nil)
            :else (unify s u v))))

      :else nil)))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; BEGIN HORRIBLE HACK
;;;;;;;;;;;;;;;;;;;;; only 2 lines have been added to the original, duly noted below

(in-ns 'clojure.core.logic)
(require '[clojure.math.combinatorics :refer [permutations]])
(deftype LCons [a d ^{:unsynchronized-mutable true :tag int} cache meta]
  ITreeTerm
  clojure.lang.IObj
  (meta [this]
    meta)
  (withMeta [this new-meta]
    (LCons. a d cache new-meta))

  LConsSeq
  (lfirst [_] a)
  (lnext [_] d)

  LConsPrint
  (toShortString [this]
    (cond
     (.. this getClass (isInstance d)) (str a " " (toShortString d))
     :else (str a " . " d )))

  Object
  (toString [this] (cond
                    (.. this getClass (isInstance d))
                      (str "(" a " " (toShortString d) ")")
                    :else (str "(" a " . " d ")")))

  (equals [this o]
    (or (identical? this o)
        (and (.. this getClass (isInstance o))
             (loop [me this
                    you o]
               (cond
                (nil? me) (nil? you)
                (lvar? me) true
                (lvar? you) true
                (and (lcons? me) (lcons? you))
                  (let [mef  (lfirst me)
                        youf (lfirst you)]
                    (and (or (= mef youf)
                             (lvar? mef)
                             (lvar? youf))
                         (recur (lnext me) (lnext you))))
                :else (= me you))))))

  (hashCode [this]
    (if (clojure.core/== cache -1)
      (do
        (set! cache (uai (umi (int 31) (clojure.lang.Util/hash d))
                         (clojure.lang.Util/hash a)))
        cache)
      cache))

  IUnifyTerms
  (unify-terms [u v s]
    (cond
      (sequential? v)
      (loop [u u v (seq v) s s]
        (if-not (nil? v)
          (if (lcons? u)
            (if-let [s (unify s (lfirst u) (first v))]
              (recur (lnext u) (next v) s)
              nil)
            (unify s u v))
          (if (lvar? u)
            (if-let [s (unify s u '())]
              s
              (unify s u nil))
            nil)))

      ;; This was added to the original
      (or (map? v)(set? v))
      (reduce #(mplus % (-inc %2))
              (for [p (permutations v)] (unify s u p)))

      (lcons? v)
      (loop [u u v v s s]
        (if (lvar? u)
          (unify s u v)
          (cond
            (lvar? v) (unify s v u)
            (and (lcons? u) (lcons? v))
            (if-let [s (unify s (lfirst u) (lfirst v))]
              (recur (lnext u) (lnext v) s)
              nil)
            :else (unify s u v))))

      :else nil))

  IReifyTerm
  (reify-term [v s]
    (loop [v v s s]
      (if (lcons? v)
        (recur (lnext v) (-reify* s (lfirst v)))
        (-reify* s v))))

  ;; TODO: no way to make this non-stack consuming w/o a lot more thinking
  ;; we could use continuation passing style and trampoline
  IWalkTerm
  (walk-term [v f]
    (lcons (f (lfirst v))
           (f (lnext v))))

  IOccursCheckTerm
  (occurs-check-term [v x s]
    (loop [v v x x s s]
      (if (lcons? v)
        (or (occurs-check s x (lfirst v))
            (recur (lnext v) x s))
        (occurs-check s x v))))

  IBuildTerm
  (build-term [u s]
    (loop [u u s s]
      (if (lcons? u)
        (recur (lnext u) (build s (lfirst u)))
        (build s u)))))
(in-ns 'naiveclpset.main)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; END HORRIBLE HACK

(comment
  ;; Unifying with LCons now works (kinda, see below, not all options given)
  (run* [p q] (conso p q #{[:a 1] [:b 2]}))
  (run* [p q] (conso p q {:a 1 :b 2}))
  (run* [q] (== (lcons 1 (lcons 2 q)) #{3 2 1})) ; Apparently I'm allowing unification of ordered and unordered topics

  (run* [q] (firsto #{q} 1))
  (run* [q] (firsto #{:a 2} q)) ; Relationally, we should be more formal than clojure: (first #{3 2}) => 3 and produce all possible options
  (run* [q] (firsto {:a 1 :b 2} q))
)
