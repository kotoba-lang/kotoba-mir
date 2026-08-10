(ns kotoba.mir-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.gmir :as gmir]
            [kotoba.mir :as mir]))

(def v0 (gmir/vreg 0))
(def v1 (gmir/vreg 1))
(def v2 (gmir/vreg 2))
(def v3 (gmir/vreg 3))

(def program
  {:gmir/version 1
   :gmir/instructions
   [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
    {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 1}
    {:gmir/op :gmir/add :gmir/dst v2 :gmir/left v0 :gmir/right v1}
    {:gmir/op :gmir/return :gmir/value v2}]})

(deftest selection-is-target-explicit-and-preserves-vregs
  (doseq [target mir/targets]
    (let [selected (mir/select-target target program)]
      (is (= target (:mir/target selected)))
      (is (= :virtual (:mir/registers selected)))
      (is (= :mir/add (get-in selected [:mir/instructions 2 :mir/op])))
      (is (= v2 (get-in selected [:mir/instructions 2 :mir/dst]))))))

(deftest allocation-is-deterministic-and-physical
  (doseq [target mir/targets]
    (let [selected (mir/select-target target program)
          first-result (mir/allocate-registers selected)
          second-result (mir/allocate-registers selected)]
      (is (= first-result second-result))
      (is (= :physical (:mir/registers first-result)))
      (is (zero? (:mir/frame-slots first-result)))
      (is (not-any? gmir/vreg? (tree-seq coll? seq first-result))))))

(deftest selection-and-allocation-cover-the-i64-scalar-family
  (doseq [op [:gmir/add :gmir/subtract :gmir/multiply :gmir/quotient
              :gmir/bit-and :gmir/bit-or :gmir/bit-xor
              :gmir/equal :gmir/less-than :gmir/greater-than
              :gmir/less-or-equal :gmir/greater-or-equal]]
    (let [input (assoc-in program [:gmir/instructions 2 :gmir/op] op)
          allocated (->> input (mir/select-target :aarch64)
                         mir/allocate-registers)]
      (is (= (keyword "mir" (name op))
             (get-in allocated [:mir/instructions 2 :mir/op]))))))

(deftest allocation-spills-deterministically-when-the-scratch-profile-is-exhausted
  (let [registers (mapv gmir/vreg (range 6))
        program {:gmir/version 1
                 :gmir/instructions
                 (vec (concat
                       (map-indexed (fn [index register]
                                      {:gmir/op :gmir/constant :gmir/dst register
                                       :gmir/value index})
                                    registers)
                       [{:gmir/op :gmir/add :gmir/dst (gmir/vreg 6)
                         :gmir/left (first registers) :gmir/right (last registers)}
                        {:gmir/op :gmir/return :gmir/value (gmir/vreg 6)}]))}
        allocated (->> program (mir/select-target :x86-64) mir/allocate-registers)]
    (is (= 7 (:mir/frame-slots allocated)))
    (is (= allocated
           (->> program (mir/select-target :x86-64) mir/allocate-registers)))
    (is (some #(= :mir/spill-store (:mir/op %)) (:mir/instructions allocated)))
    (is (some #(= :mir/spill-load (:mir/op %)) (:mir/instructions allocated)))
    (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)))))

(deftest allocation-fails-closed
  (testing "use before definition"
    (is (thrown? clojure.lang.ExceptionInfo
                 (->> {:gmir/version 1
                       :gmir/instructions [{:gmir/op :gmir/return :gmir/value v0}]}
                      (mir/select-target :x86-64)
                      mir/allocate-registers))))
  (testing "spill fallback cannot make a future definition visible"
    (let [registers (mapv gmir/vreg (range 7))]
      (is (thrown? clojure.lang.ExceptionInfo
                   (->> {:gmir/version 1
                         :gmir/instructions
                         (vec (concat
                               (map-indexed (fn [index register]
                                              {:gmir/op :gmir/constant
                                               :gmir/dst register
                                               :gmir/value index})
                                            (take 5 registers))
                               [{:gmir/op :gmir/return
                                 :gmir/value (last registers)}
                                {:gmir/op :gmir/constant
                                 :gmir/dst (last registers)
                                 :gmir/value 6}]))}
                        (mir/select-target :x86-64)
                        mir/allocate-registers)))))
  (testing "foreign physical registers"
    (is (thrown? clojure.lang.ExceptionInfo
                 (mir/validate!
                  {:mir/version 1
                   :mir/target :aarch64
                   :mir/registers :physical
                   :mir/instructions
                   [{:mir/op :mir/return :mir/value :x86-64/rax}]}))))
  (testing "unsupported target"
    (is (thrown? clojure.lang.ExceptionInfo
                 (mir/select-target :riscv64 program))))
  (testing "MIR control flow is closed even when it did not come from GMIR"
    (let [base {:mir/version 1
                :mir/target :x86-64
                :mir/registers :physical
                :mir/instructions
                [{:mir/op :mir/label :mir/id :test.label/entry}
                 {:mir/op :mir/jump :mir/target :test.label/missing}]}]
      (is (thrown? clojure.lang.ExceptionInfo (mir/validate! base)))
      (is (thrown? clojure.lang.ExceptionInfo
                   (mir/validate!
                    (update base :mir/instructions
                            (fn [instructions]
                              (-> instructions
                                  (assoc-in [1 :mir/target] :test.label/entry)
                                  (conj {:mir/op :mir/label
                                         :mir/id :test.label/entry}))))))))))

(def phi-program
  {:gmir/version 2
   :gmir/instructions
   [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
    {:gmir/op :gmir/branch-zero :gmir/test v0 :gmir/target :test.label/else}
    {:gmir/op :gmir/label :gmir/id :test.label/then}
    {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 11}
    {:gmir/op :gmir/label :gmir/id :test.label/then-exit}
    {:gmir/op :gmir/jump :gmir/target :test.label/join}
    {:gmir/op :gmir/label :gmir/id :test.label/else}
    {:gmir/op :gmir/constant :gmir/dst v2 :gmir/value 22}
    {:gmir/op :gmir/label :gmir/id :test.label/else-exit}
    {:gmir/op :gmir/jump :gmir/target :test.label/join}
    {:gmir/op :gmir/label :gmir/id :test.label/join}
    {:gmir/op :gmir/phi :gmir/dst v3
     :gmir/incomings [{:gmir/predecessor :test.label/then-exit :gmir/value v1}
                      {:gmir/predecessor :test.label/else-exit :gmir/value v2}]}
    {:gmir/op :gmir/return :gmir/value v3}]})

(deftest single-phi-join-coalesces-to-direct-edge-moves
  (doseq [target mir/targets]
    (let [selected (mir/select-target target phi-program)
          allocated (mir/allocate-registers selected)
          instructions (:mir/instructions allocated)]
      (is (= 2 (:mir/version selected)))
      (is (zero? (:mir/frame-slots allocated)))
      (is (= 2 (count (filter #(= :mir/move (:mir/op %)) instructions))))
      (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load} (:mir/op %))
                    instructions))
      (is (not-any? #(= :mir/phi (:mir/op %)) instructions))
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)))
      (is (= allocated (mir/allocate-registers selected))))))

(def dual-phi-program
  (let [values (mapv gmir/vreg (range 8))
        [test then-a then-b else-a else-b join-a join-b result] values]
    {:gmir/version 2
     :gmir/instructions
     [{:gmir/op :gmir/argument :gmir/dst test :gmir/index 0}
      {:gmir/op :gmir/branch-zero :gmir/test test :gmir/target :test.label/else}
      {:gmir/op :gmir/label :gmir/id :test.label/then}
      {:gmir/op :gmir/constant :gmir/dst then-a :gmir/value 1}
      {:gmir/op :gmir/constant :gmir/dst then-b :gmir/value 2}
      {:gmir/op :gmir/label :gmir/id :test.label/then-exit}
      {:gmir/op :gmir/jump :gmir/target :test.label/join}
      {:gmir/op :gmir/label :gmir/id :test.label/else}
      {:gmir/op :gmir/constant :gmir/dst else-a :gmir/value 3}
      {:gmir/op :gmir/constant :gmir/dst else-b :gmir/value 4}
      {:gmir/op :gmir/label :gmir/id :test.label/else-exit}
      {:gmir/op :gmir/jump :gmir/target :test.label/join}
      {:gmir/op :gmir/label :gmir/id :test.label/join}
      {:gmir/op :gmir/phi :gmir/dst join-a
       :gmir/incomings [{:gmir/predecessor :test.label/then-exit :gmir/value then-a}
                        {:gmir/predecessor :test.label/else-exit :gmir/value else-a}]}
      {:gmir/op :gmir/phi :gmir/dst join-b
       :gmir/incomings [{:gmir/predecessor :test.label/then-exit :gmir/value then-b}
                        {:gmir/predecessor :test.label/else-exit :gmir/value else-b}]}
      {:gmir/op :gmir/add :gmir/dst result :gmir/left join-a :gmir/right join-b}
      {:gmir/op :gmir/return :gmir/value result}]}))

(deftest multi-phi-join-keeps-frame-fallback-without-parallel-copy-scheduler
  (doseq [target mir/targets]
    (let [allocated (->> dual-phi-program (mir/select-target target) mir/allocate-registers)
          instructions (:mir/instructions allocated)]
      (is (= 2 (:mir/frame-slots allocated)))
      (is (= 4 (count (filter #(= :mir/spill-store (:mir/op %)) instructions))))
      (is (= 2 (count (filter #(= :mir/spill-load (:mir/op %)) instructions))))
      (is (not-any? #(= :mir/move (:mir/op %)) instructions)))))

(deftest phi-merge-slots-remain-disjoint-from-general-spills
  (let [registers (mapv gmir/vreg (range 8))
        [test a b c d e then-value else-value] registers
        join-value (gmir/vreg 8)
        result (gmir/vreg 9)
        input {:gmir/version 2
               :gmir/instructions
               [{:gmir/op :gmir/constant :gmir/dst test :gmir/value 1}
                {:gmir/op :gmir/constant :gmir/dst a :gmir/value 1}
                {:gmir/op :gmir/constant :gmir/dst b :gmir/value 2}
                {:gmir/op :gmir/constant :gmir/dst c :gmir/value 3}
                {:gmir/op :gmir/constant :gmir/dst d :gmir/value 4}
                {:gmir/op :gmir/constant :gmir/dst e :gmir/value 5}
                {:gmir/op :gmir/branch-zero :gmir/test test :gmir/target :test.label/else}
                {:gmir/op :gmir/label :gmir/id :test.label/then}
                {:gmir/op :gmir/add :gmir/dst then-value :gmir/left a :gmir/right b}
                {:gmir/op :gmir/label :gmir/id :test.label/then-exit}
                {:gmir/op :gmir/jump :gmir/target :test.label/join}
                {:gmir/op :gmir/label :gmir/id :test.label/else}
                {:gmir/op :gmir/add :gmir/dst else-value :gmir/left c :gmir/right d}
                {:gmir/op :gmir/label :gmir/id :test.label/else-exit}
                {:gmir/op :gmir/jump :gmir/target :test.label/join}
                {:gmir/op :gmir/label :gmir/id :test.label/join}
                {:gmir/op :gmir/phi :gmir/dst join-value
                 :gmir/incomings
                 [{:gmir/predecessor :test.label/then-exit :gmir/value then-value}
                  {:gmir/predecessor :test.label/else-exit :gmir/value else-value}]}
                {:gmir/op :gmir/add :gmir/dst result :gmir/left join-value :gmir/right e}
                {:gmir/op :gmir/return :gmir/value result}]}
        allocated (->> input (mir/select-target :x86-64) mir/allocate-registers)
        instructions (:mir/instructions allocated)]
    (is (= 10 (:mir/frame-slots allocated))
        "the phi destination owns its ordinary spill slot; no extra merge slot exists")
    (is (not-any? #(= :mir/move (:mir/op %)) instructions)
        "the general spill path coalesces slots instead of introducing moves")
    (is (not-any? #(= :mir/phi (:mir/op %)) (:mir/instructions allocated)))))
