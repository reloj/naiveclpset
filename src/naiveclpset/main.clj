(ns naiveclpset.main
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :refer :all]
            [clojure.core.logic.protocols :refer :all]
            [clojure.set]
            [clojure.math.combinatorics :refer [permutations]]))

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
      (when (= (count u) (count v))
        (let [uu (clojure.set/difference u v)
              vv (clojure.set/difference v u)
              u (seq uu)
              v (seq vv)]
          (reduce #(mplus % (-inc %2))
                  (for [p (permutations u)] (unify s p v)))))
        ;; TODO unify-terms should return a substitution, not a stream of substitutions, right?

        ;; alternative higher-level version
        ;((or* (for [p (permutations u)]
        ;         (== p v))) s)


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
  (run* [q] (fresh [a1 a2 a3] (== #{a1 a2 a3} #{1 2 3}) (== q [a1 a2 a3]))) ; 6 results, this is ok!
  (run* [q] (== #{1 2 [3 q]} #{1 2 [3 4]}))
  (run* [q] (== [1 2 #{3 q}] [1 2 #{3 4}]))
  (run* [q] (== #{1 2 #{3 q}} #{1 2 #{3 4}})) ; fails (sometimes!?) as Choice cannot be walked --> not for the moment, as I trim the sets prior to unification
  (run* [q] (== #{ #{ #{q} :bar} :baz}  #{:baz #{:bar #{:foo}}}))

  ;; Note that sets are "unordered", they should not unify with something with order! They aren't really the same if only one has an order, right? Use permuteo otherwise!
  (run* [q] (== [1 2 3] #{3 2 1}))
  (run* [q] (permuteo [1 2 3] #{3 2 1})) ; TO DO should not return 6 _0 just 1

  ;; a set of kv vectors should unify with a map
  (run* [q] (== #{[:a 1]} #{[:a q]}))
  (run* [q] (== #{[:a 1]} {:a q}))
  (run* [q] (== {:a 1} #{[:a q]}))

  ;; TO DO a map is more restrictive than just a set of kvs
  (run* [q] (== {:a 1 q 2} #{[:a 1] [:a 2]})) ; TO DO should not unify (q cant be :a as :a exists elsewhere)

  ;; TO DO unable to unify on keys
  (run* [q] (== {:a 1} {q 1})) ; TO DO should return :a
  (run* [q] (== {:a 1} {q 1 :b 1}))
  (run* [q] (== {:a 1} {q 1 :b 2}))
  (run* [k v] (== #{[:a 1]} {k v})) ; note that this DOES work!
  (run* [q] (== [q] {:a 1})) ; Thus no construction of a map is possible based on kv pairs.
  )


(comment
  ;; not clpset, but maps should unify based only on common keys
  (run* [q] (== {:a q} {:a 1 :b 2}))) ; I think this is why featureo exists
  ;; here david nolen has some opinion on maps.
  ;; https://groups.google.com/g/clojure/c/6n7Y7D4Hbc4?pli=1
  ;; also I went in other direction:
  ;; https://github.com/reloj/oclock/blob/master/src/reloj/oclock.clj




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
      (let [uu (clojure.set/difference u v)
            vv (clojure.set/difference v u)
            u (seq uu)
            v (seq vv)]
        (reduce #(mplus % (-inc %2))
                (for [p (permutations u)] (unify s p v))))
      ;; TODO unify-terms should return a substitution, not a stream of substitutions, right?

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
;;;;;;;;;;;;;;;;;;;;; only a handful of lines have been added to the original, duly noted below

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
      (let [uu (clojure.set/difference u v)
            vv (clojure.set/difference v u)
            u (seq uu)
            v (seq vv)]
        (reduce #(mplus % (-inc %2))
                (for [p (permutations u)] (unify s p v))))
      ;; TODO unify-terms should return a substitution, not a stream of substitutions, right?

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

;; General comment here: does it make sense to unify ordered and unordered things directly? shouldn't I need to use a kind of permuteo relation?
;; Answer. It is practical as cons is used in several places where it makes sense to sequence a set, e.g. in defne. although ideally I'd find those places and change them. So... no?

(comment
  ;; Unifying with LCons now works
  (run* [p q] (conso p q #{[:a 1] [:b 2]}))
  (run* [p q] (conso p q {:a 1 :b 2})) ; TODO conso loses the "map form"
  (run* [q] (== (lcons 1 (lcons 2 q)) #{3 2 1})) ; Apparently I'm allowing unification of ordered and unordered topics

  (run* [q] (firsto #{q} 1))
  (run* [q] (firsto #{:a 2} q)) ; Relationally, we should be more formal than clojure: (first #{3 2}) => 3 and produce all possible options
  (run* [q] (firsto {:a 1 :b 2} q))
)

;; Conso kills the lack of order (first run works as expected, second run surprises)
  (run* [q] (== #{1 2 (lvar) 4 5}
                #{5 4 q 2 1}))
  (run* [q]
    (fresh [a b c complete]
      (== [a c] [#{1 2} #{4 5}])
      (appendo a [(lvar)] b)
      (appendo b c complete)
      ;(== complete #{5 4 q 2 1})
      (== q complete)
      ))

(defne featureo [m kvmap]
  ([m []]) ; trivial case where no feature is required

  ([[kv] [kv]])

  ([[mhead . mtail] [kv . nil]] ; base case for just one key-value pair (one feature)
   (!= mtail nil)
   (conde [(== mhead kv)]
          [(featureo mtail kvmap)])) ; do I iterate infinitely with nil not being empty here? I did not test it.

  ([m [kvhead . kvtail]] ; recursion for multiple kvs
   (!= kvtail nil)
   (featureo m [kvhead])
   (featureo m kvtail)))

(defne any-placeo ; from oclock
  "A generalization of membero and rembero, and, backwards, a 'random-popo'."
  [x l o]
  ([_ _ [x . l]])
  ([_ [l1 . ls] [l1 . os]]
   (any-placeo x ls os)))

(defne featureo [m kvmap]
  ([m []])
  ([m [kvhead . kvtail]] ; recursion for multiple kvs
   (fresh [m2]
     (any-placeo kvhead m2 m)
     (featureo m2 kvtail))))


(comment ; featureo tests
  (run* [q] (featureo q {:a 1}))
  (run 2 [q] (featureo q {:a 1}) (featureo q {:a 2})) ; ought to fail but not implemented very above
  (run 1 [q] (featureo q {:a 1}) (featureo q {:b 2})) ; should return a set
  (run 5 [q] (featureo q {:a 1}) (featureo q {:b 2})) ; WRONG! repeats results and considers order
  (run 5 [q] (featureo {:a 1} {:a q}))
  (run* [q] (featureo {:a 1} {q 1}))

  (run 3 [q] (featureo {:a q :b 2} {:a 1})) ; infinite results! should I make it a constrain? minikanren typically diverges, while not providing any further info... perhaps there is a way to enhance it.

  ;; TO DO test good integration of featureo and featurec

  (run 15 [q]
    (featureo q {:size :small})
    (fresh [f]
      (membero f [:strawberry :vanilla :chocolate])
      (featureo q {:flavour f}))
    (fresh [x y z] ; to constrain size ;;;;;;;;;;;;;; TO DO this does not work
      (== q [x y z])))

  )

(comment ; featureo is a handy function to talk about partial maps
  (run 5 [kv] (featureo {:a 1 :b 2} kv)) ; TO DO repeats elements of the feature powerset
  (run 5 [k v] (featureo {:a 1 :b 2} {k v})) ; Interestingly this works!

  (run 5 [m] (featureo m {:a 1 :b 2}))
  (run 5 [m k v] (featureo m {k v}))

  (run 2 [m]  ; TO DO does not conserve this as a map
    (featureo m {:a 1 :b 2})
    (featureo m {:c 3}))

  (run 2 [m]  ; TO DO creates a non-map as :a has two incompatible values
    (featureo m {:a 1 :b 2})
    (featureo m {:a 3}))
)
