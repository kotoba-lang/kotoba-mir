(ns kotoba.mir-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.gmir :as gmir]
            [kotoba.mir :as mir]))

(def v0 (gmir/vreg 0))
(def v1 (gmir/vreg 1))
(def v2 (gmir/vreg 2))

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
