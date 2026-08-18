(ns kotoba.mir-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.gmir :as gmir]
            [clojure.set]
            [kotoba.mir :as mir]))

(defmacro with-scratch-tier-only
  "Run BODY with only the always-available scratch tier on offer. Tests that
  are about what happens when the profile is exhausted have to be able to
  exhaust it; otherwise widening the pool turns them into tests of nothing
  that keep passing under their original names."
  [& body]
  `(with-redefs [mir/leaf-registers {:x86-64 [] :aarch64 []}
                 mir/preserved-registers {:x86-64 [] :aarch64 []}]
     ~@body))

(def v0 (gmir/vreg 0))
(def v1 (gmir/vreg 1))
(def v2 (gmir/vreg 2))
(def v3 (gmir/vreg 3))
(def v4 (gmir/vreg 4))
(def v5 (gmir/vreg 5))
(def v6 (gmir/vreg 6))

(deftest allocated-aarch64-admits-canonical-fused-multiply-operations
  (let [base {:mir/version 1 :mir/target :aarch64 :mir/registers :physical
              :mir/frame-slots 0}
        instruction (fn [op]
                      {:mir/op op :mir/dst :aarch64/x0
                       :mir/left :aarch64/x1 :mir/right :aarch64/x2
                       :mir/addend :aarch64/x3})]
    (doseq [op [:mir/multiply-add :mir/multiply-subtract]]
      (let [program (assoc base :mir/instructions
                           [(instruction op)
                            {:mir/op :mir/return :mir/value :aarch64/x0}])]
        (is (= program (mir/validate! program)) op)
        (is (thrown? clojure.lang.ExceptionInfo
                     (mir/validate! (update-in program [:mir/instructions 0]
                                               dissoc :mir/addend))) op)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (mir/validate!
                  {:mir/version 1 :mir/target :aarch64 :mir/registers :virtual
                   :mir/instructions
                   [{:mir/op :mir/multiply-add :mir/dst v0 :mir/left v1
                     :mir/right v2 :mir/addend v3}]}))
        "fusion is a physical target-selection operation")))

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
              :gmir/shift-left :gmir/shift-right-signed
              :gmir/shift-right-unsigned
              :gmir/equal :gmir/less-than :gmir/greater-than
              :gmir/less-or-equal :gmir/greater-or-equal]]
    (let [input (assoc-in program [:gmir/instructions 2 :gmir/op] op)
          allocated (->> input (mir/select-target :aarch64)
                         mir/allocate-registers)]
      (is (= (keyword "mir" (name op))
             (get-in allocated [:mir/instructions 2 :mir/op]))))))

(deftest v3-selection-elides-an-exclusively-consumed-constant-divisor
  (let [module {:gmir/version 3 :gmir/entry 'kernel
                :gmir/functions
                [{:gmir/name 'kernel :gmir/arity 1
                  :gmir/instructions
                  [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                   {:gmir/op :gmir/constant :gmir/dst v1
                    :gmir/value 2147483647}
                   {:gmir/op :gmir/quotient :gmir/dst v2
                    :gmir/left v0 :gmir/right v1}
                   {:gmir/op :gmir/return :gmir/value v2}]}]}
        selected (mir/select-target :aarch64 module)
        selected-instructions (get-in selected [:mir/functions 0 :mir/instructions])
        quotient (first (filter #(= :mir/quotient-constant (:mir/op %))
                                selected-instructions))
        allocated (mir/allocate-registers selected)
        physical (first (filter #(= :mir/quotient-constant (:mir/op %))
                                (get-in allocated [:mir/functions 0
                                                   :mir/instructions])))]
    (is (= :mir/quotient-constant (:mir/op quotient)))
    (is (= 2147483647 (:mir/divisor quotient)))
    (is (not (contains? quotient :mir/right)))
    (is (not-any? #(= v1 (:mir/dst %)) selected-instructions)
        "the divisor definition is dead after the literal enters MIR")
    (is (= 2147483647 (:mir/divisor physical)))
    (is (not (contains? physical :mir/right)))
    (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)))))

(deftest v3-selection-preserves-a-constant-divisor-with-another-use
  (let [module {:gmir/version 3 :gmir/entry 'kernel
                :gmir/functions
                [{:gmir/name 'kernel :gmir/arity 1
                  :gmir/instructions
                  [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                   {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 7}
                   {:gmir/op :gmir/quotient :gmir/dst v2
                    :gmir/left v0 :gmir/right v1}
                   {:gmir/op :gmir/add :gmir/dst v3
                    :gmir/left v2 :gmir/right v1}
                   {:gmir/op :gmir/return :gmir/value v3}]}]}
        selected (mir/select-target :x86-64 module)
        selected-instructions (get-in selected [:mir/functions 0 :mir/instructions])]
    (is (= :mir/constant (:mir/op (second selected-instructions))))
    (is (= v1 (:mir/dst (second selected-instructions))))
    (is (= :mir/quotient-constant (:mir/op (nth selected-instructions 2))))
    (is (not (contains? (nth selected-instructions 2) :mir/right)))
    (is (= v1 (:mir/right (nth selected-instructions 3))))))

(deftest selection-and-allocation-cover-the-f64-family
  (doseq [target mir/targets
          op [:gmir/f64-add :gmir/f64-subtract :gmir/f64-multiply
              :gmir/f64-divide :gmir/f64-min :gmir/f64-max
              :gmir/f64-equal :gmir/f64-less-than :gmir/f64-less-or-equal
              :gmir/f64-greater-than :gmir/f64-greater-or-equal
              :gmir/f64-unordered]]
    (let [input (assoc-in program [:gmir/instructions 2 :gmir/op] op)
          selected (mir/select-target target input)
          allocated (mir/allocate-registers selected)]
      (is (= (keyword "mir" (name op))
             (get-in selected [:mir/instructions 2 :mir/op])))
      (is (some #(= (keyword "mir" (name op)) (:mir/op %))
                (:mir/instructions allocated)))))
  (doseq [target mir/targets]
    (let [input (assoc program :gmir/instructions
                       [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                        {:gmir/op :gmir/f64-sqrt :gmir/dst v1 :gmir/input v0}
                        {:gmir/op :gmir/return :gmir/value v1}])
          selected (mir/select-target target input)
          allocated (mir/allocate-registers selected)]
      (is (= :mir/f64-sqrt
             (get-in selected [:mir/instructions 1 :mir/op])))
      (is (some #(= :mir/f64-sqrt (:mir/op %)) (:mir/instructions allocated)))
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated))))))

(deftest f64-allocation-spills-binary-and-unary-values
  (with-scratch-tier-only
    (let [registers (mapv gmir/vreg (range 11))
          program {:gmir/version 1
                   :gmir/instructions
                   (vec (concat
                         (map-indexed (fn [index register]
                                        {:gmir/op :gmir/constant :gmir/dst register
                                         :gmir/value (+ 4607182418800017408 index)})
                                      (subvec registers 0 6))
                         [{:gmir/op :gmir/f64-add :gmir/dst (registers 6)
                           :gmir/left (registers 0) :gmir/right (registers 1)}
                          {:gmir/op :gmir/f64-multiply :gmir/dst (registers 7)
                           :gmir/left (registers 2) :gmir/right (registers 3)}
                          {:gmir/op :gmir/f64-unordered :gmir/dst (registers 8)
                           :gmir/left (registers 4) :gmir/right (registers 5)}
                          {:gmir/op :gmir/f64-add :gmir/dst (registers 9)
                           :gmir/left (registers 6) :gmir/right (registers 7)}
                          {:gmir/op :gmir/f64-sqrt :gmir/dst (registers 10)
                           :gmir/input (registers 9)}
                          {:gmir/op :gmir/return :gmir/value (registers 10)}]))}
          allocated (->> program (mir/select-target :x86-64)
                         mir/allocate-registers)]
      (is (= 11 (:mir/frame-slots allocated)))
      (is (some #(= :mir/f64-sqrt (:mir/op %)) (:mir/instructions allocated)))
      (is (some #(= :mir/f64-unordered (:mir/op %)) (:mir/instructions allocated)))
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated))))))

(deftest selection-and-allocation-cover-bounded-kernel-memory
  (let [prefix [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                {:gmir/op :gmir/argument :gmir/dst v1 :gmir/index 1}
                {:gmir/op :gmir/argument :gmir/dst v2 :gmir/index 2}
                {:gmir/op :gmir/argument :gmir/dst v3 :gmir/index 3}]
        operations
        [{:gmir/op :gmir/kernel-load-u8 :gmir/dst v4
          :gmir/base v0 :gmir/length v1 :gmir/index v2 :gmir/maximum 512}
         {:gmir/op :gmir/kernel-load-u32 :gmir/dst v4
          :gmir/base v0 :gmir/length v1 :gmir/index v2 :gmir/maximum 512}
         {:gmir/op :gmir/kernel-store-u8 :gmir/dst v4
          :gmir/base v0 :gmir/length v1 :gmir/index v2 :gmir/stored v3
          :gmir/maximum 4096}
         {:gmir/op :gmir/kernel-store-u32 :gmir/dst v4
          :gmir/base v0 :gmir/length v1 :gmir/index v2 :gmir/stored v3
          :gmir/maximum 512}
         {:gmir/op :gmir/kernel-subregion :gmir/dst v4
          :gmir/base v0 :gmir/length v1 :gmir/offset v2 :gmir/size v3}]]
    (doseq [target mir/targets, operation operations]
      (let [program {:gmir/version 1
                     :gmir/instructions
                     (conj prefix operation
                           {:gmir/op :gmir/return :gmir/value v4})}
            selected (mir/select-target target program)
            allocated (mir/allocate-registers selected)
            mir-op (keyword "mir" (name (:gmir/op operation)))]
        (is (= mir-op (get-in selected [:mir/instructions 4 :mir/op])))
        (is (some #(= mir-op (:mir/op %)) (:mir/instructions allocated)))
        (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)))))))

(deftest x86-privileged-selection-is-target-scoped-and-allocatable
  (let [program {:gmir/version 3 :gmir/entry 'main
                 :gmir/functions
                 [{:gmir/name 'main :gmir/arity 0
                   :gmir/instructions
                   [{:gmir/op :gmir/constant :gmir/dst v0 :gmir/value 1}
                    {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 2}
                    {:gmir/op :gmir/x86-privileged :gmir/dst v2
                     :gmir/action :write-msr :gmir/arguments [v0 v1]}
                    {:gmir/op :gmir/return :gmir/value v2}]}]}
        selected (mir/select-target :x86-64 program)
        allocated (mir/allocate-registers selected)
        operation (first (filter #(= :mir/x86-privileged (:mir/op %))
                                 (get-in allocated [:mir/functions 0
                                                    :mir/instructions])))]
    (is (= :write-msr (:mir/action operation)))
    (is (= 2 (count (:mir/arguments operation))))
    (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"x86-privileged-target-mismatch"
                          (mir/select-target :aarch64 program)))))

(deftest allocation-spills-deterministically-when-the-scratch-profile-is-exhausted
  (with-scratch-tier-only
    (let [registers (mapv gmir/vreg (range 11))
          program {:gmir/version 1
                   :gmir/instructions
                   (vec (concat
                         (map-indexed (fn [index register]
                                        {:gmir/op :gmir/constant :gmir/dst register
                                         :gmir/value index})
                                      (subvec registers 0 6))
                         [{:gmir/op :gmir/add :gmir/dst (registers 6)
                           :gmir/left (registers 0) :gmir/right (registers 1)}
                          {:gmir/op :gmir/add :gmir/dst (registers 7)
                           :gmir/left (registers 2) :gmir/right (registers 3)}
                          {:gmir/op :gmir/add :gmir/dst (registers 8)
                           :gmir/left (registers 4) :gmir/right (registers 5)}
                          {:gmir/op :gmir/add :gmir/dst (registers 9)
                           :gmir/left (registers 6) :gmir/right (registers 7)}
                          {:gmir/op :gmir/add :gmir/dst (registers 10)
                           :gmir/left (registers 9) :gmir/right (registers 8)}
                          {:gmir/op :gmir/return :gmir/value (registers 10)}]))}
          allocated (->> program (mir/select-target :x86-64) mir/allocate-registers)]
      (is (= 11 (:mir/frame-slots allocated)))
      (is (= allocated
             (->> program (mir/select-target :x86-64) mir/allocate-registers)))
      (is (some #(= :mir/spill-store (:mir/op %)) (:mir/instructions allocated)))
      (is (some #(= :mir/spill-load (:mir/op %)) (:mir/instructions allocated)))
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated))))))

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
      (is (= (if (= :x86-64 target) 3 2)
             (count (filter #(= :mir/move (:mir/op %)) instructions))))
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

(deftest acyclic-multi-phi-join-coalesces-to-direct-edge-moves
  (with-scratch-tier-only
    (doseq [target mir/targets]
      (let [allocated (->> dual-phi-program (mir/select-target target) mir/allocate-registers)
            instructions (:mir/instructions allocated)]
        (is (zero? (:mir/frame-slots allocated)))
        (is (= (if (= :x86-64 target) 3 2)
               (count (filter #(= :mir/move (:mir/op %)) instructions))))
        (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load} (:mir/op %))
                      instructions))
        (is (= allocated
               (->> dual-phi-program (mir/select-target target) mir/allocate-registers)))))))

(deftest cyclic-multi-phi-join-uses-one-reusable-temporary-slot
  (doseq [target mir/targets]
    (let [[r0 r1 r2] (get mir/physical-registers target)
          schedule #'kotoba.mir/schedule-parallel-copies
          swap (schedule [{:mir/dst r0 :mir/src r1}
                          {:mir/dst r1 :mir/src r0}]
                         7)
          duplicate-source-cycle
          (schedule [{:mir/dst r0 :mir/src r1}
                     {:mir/dst r2 :mir/src r1}
                     {:mir/dst r1 :mir/src r0}]
                    7)]
      (is (:used-temp? swap))
      (is (= [{:mir/op :mir/spill-store :mir/src r1 :mir/slot 7}
              {:mir/op :mir/move :mir/dst r1 :mir/src r0}
              {:mir/op :mir/spill-load :mir/dst r0 :mir/slot 7}]
             (:instructions swap)))
      (is (= [{:mir/op :mir/move :mir/dst r2 :mir/src r1}
              {:mir/op :mir/spill-store :mir/src r1 :mir/slot 7}
              {:mir/op :mir/move :mir/dst r1 :mir/src r0}
              {:mir/op :mir/spill-load :mir/dst r0 :mir/slot 7}]
             (:instructions duplicate-source-cycle)))
      (is (= swap
             (schedule [{:mir/dst r0 :mir/src r1}
                        {:mir/dst r1 :mir/src r0}]
                       7))))))

(defn- source-vectors [values width]
  (if (zero? width)
    [[]]
    (mapcat (fn [value]
              (map #(into [value] %)
                   (source-vectors values (dec width))))
            values)))

(defn- execute-copy-schedule [register-state instructions]
  (:registers
   (reduce (fn [{:keys [registers temp] :as state}
                {:mir/keys [op dst src]}]
             (case op
               :mir/move (assoc state :registers (assoc registers dst (get registers src)))
               :mir/spill-store (assoc state :temp (get registers src))
               :mir/spill-load (assoc state :registers (assoc registers dst temp))))
           {:registers register-state :temp nil}
           instructions)))

(deftest parallel-copy-scheduler-preserves-all-four-register-mappings
  (doseq [target mir/targets
          :let [registers (get mir/physical-registers target)
                initial (zipmap registers (range))]
          sources (source-vectors registers (count registers))]
    (let [copies (mapv (fn [dst src] {:mir/dst dst :mir/src src})
                       registers sources)
          scheduled (#'kotoba.mir/schedule-parallel-copies copies 0)
          expected (reduce (fn [state {:mir/keys [dst src]}]
                             (assoc state dst (get initial src)))
                           initial copies)]
      (is (= expected
             (execute-copy-schedule initial (:instructions scheduled)))
          (str target " " sources)))))

(deftest phi-merge-slots-remain-disjoint-from-general-spills
  (with-scratch-tier-only
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
      (is (not-any? #(= :mir/phi (:mir/op %)) (:mir/instructions allocated))))))

(def scalar-call-module
  {:gmir/version 3
   :gmir/entry 'main
   :gmir/functions
   [{:gmir/name 'add-one
     :gmir/arity 1
     :gmir/instructions
     [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
      {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 1}
      {:gmir/op :gmir/add :gmir/dst v2 :gmir/left v0 :gmir/right v1}
      {:gmir/op :gmir/return :gmir/value v2}]}
    {:gmir/name 'main
     :gmir/arity 1
     :gmir/instructions
     [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
      {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 10}
      {:gmir/op :gmir/call :gmir/dst v2 :gmir/callee 'add-one
       :gmir/arguments [v0]}
      {:gmir/op :gmir/add :gmir/dst v3 :gmir/left v1 :gmir/right v2}
      {:gmir/op :gmir/return :gmir/value v3}]}]})

(deftest v3-selects-and-allocates-independent-call-safe-function-frames
  (doseq [target mir/targets]
    (let [selected (mir/select-target target scalar-call-module)
          allocated (mir/allocate-registers selected)
          [callee caller] (:mir/functions allocated)
          call (first (filter #(= :mir/call (:mir/op %))
                              (:mir/instructions caller)))]
      (is (= 3 (:mir/version selected)) target)
      (is (= :virtual (:mir/registers selected)) target)
      (is (= :physical (:mir/registers allocated)) target)
      (is (= :allocator (:mir/frame-policy callee)) target)
      (is (zero? (:mir/frame-slots callee)) target)
      (is (= :call-live (:mir/frame-policy caller)) target)
      (is (= 1 (:mir/frame-slots caller)) target)
      (is (= 1 (count (filter #(= :mir/spill-store (:mir/op %))
                              (:mir/instructions caller)))) target)
      (is (= 1 (count (filter #(= :mir/spill-load (:mir/op %))
                              (:mir/instructions caller)))) target)
      (is (= (get mir/return-registers target) (:mir/dst call)) target)
      (is (= [(first (get mir/call-argument-registers target))]
             (:mir/arguments call)) target)
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)) target)
      (is (= allocated (->> scalar-call-module
                            (mir/select-target target)
                             mir/allocate-registers)) target))))

(deftest v3-tail-calls-release-the-current-frame-before-transfer
  (let [module (assoc-in scalar-call-module
                         [:gmir/functions 1 :gmir/instructions]
                         [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                          {:gmir/op :gmir/tail-call :gmir/callee 'add-one
                           :gmir/arguments [v0]}])]
    (doseq [target mir/targets]
      (let [caller (second (:mir/functions
                            (->> module
                                 (mir/select-target target)
                                 mir/allocate-registers)))
            tail (peek (:mir/instructions caller))]
        (is (= :call-live (:mir/frame-policy caller)) target)
        (is (= :mir/tail-call (:mir/op tail)) target)
        (is (= 'add-one (:mir/callee tail)) target)
        (is (= [(first (get mir/call-argument-registers target))]
               (:mir/arguments tail)) target)))))

(deftest v3-fifth-call-argument-is-loaded-directly-from-one-entry-slot
  (with-scratch-tier-only
    (let [args (mapv gmir/vreg (range 5))
          result (gmir/vreg 5)
          module {:gmir/version 3
                  :gmir/entry 'main
                  :gmir/functions
                  [{:gmir/name 'callee :gmir/arity 5
                    :gmir/instructions
                    (conj (mapv (fn [index register]
                                  {:gmir/op :gmir/argument :gmir/dst register
                                   :gmir/index index})
                                (range 5) args)
                          {:gmir/op :gmir/return :gmir/value v0})}
                   {:gmir/name 'main :gmir/arity 5
                    :gmir/instructions
                    (vec (concat
                          (map-indexed
                           (fn [index register]
                             {:gmir/op :gmir/argument :gmir/dst register
                              :gmir/index index}) args)
                          [{:gmir/op :gmir/call :gmir/dst result
                            :gmir/callee 'callee :gmir/arguments args}
                           {:gmir/op :gmir/return :gmir/value result}]))}]}]
      (doseq [target mir/targets]
        (let [caller (second (:mir/functions
                              (->> module (mir/select-target target)
                                   mir/allocate-registers)))
              instructions (:mir/instructions caller)
              call-index (first (keep-indexed
                                 (fn [index instruction]
                                   (when (= :mir/call (:mir/op instruction)) index))
                                 instructions))
              stores (filterv #(= :mir/spill-store (:mir/op %)) instructions)
              loads (filterv #(= :mir/spill-load (:mir/op %)) instructions)
              fifth-input (nth (get mir/call-argument-registers target) 4)]
          (is (= :call-live (:mir/frame-policy caller)) target)
          (is (= 1 (:mir/frame-slots caller)) target)
          (is (= [{:mir/op :mir/spill-store :mir/src fifth-input :mir/slot 0}]
                 stores) target)
          (is (= [{:mir/op :mir/spill-load :mir/dst fifth-input :mir/slot 0}]
                 loads) target)
          (is (= (dec call-index)
                 (first (keep-indexed (fn [index instruction]
                                        (when (= (first loads) instruction) index))
                                      instructions)))
              target))))))

(deftest v3-call-liveness-does-not-materialize-dead-values
  (let [module {:gmir/version 3
                :gmir/entry 'main
                :gmir/functions
                [{:gmir/name 'identity :gmir/arity 1
                  :gmir/instructions
                  [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                   {:gmir/op :gmir/return :gmir/value v0}]}
                 {:gmir/name 'main :gmir/arity 1
                  :gmir/instructions
                  [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                   {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 99}
                   {:gmir/op :gmir/call :gmir/dst v2
                    :gmir/callee 'identity :gmir/arguments [v0]}
                   {:gmir/op :gmir/return :gmir/value v2}]}]}]
    (doseq [target mir/targets]
      (let [caller (second (:mir/functions
                            (->> module (mir/select-target target)
                                 mir/allocate-registers)))]
        (is (= :call-live (:mir/frame-policy caller)) target)
        (is (zero? (:mir/frame-slots caller)) target)
        (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load}
                                  (:mir/op %))
                      (:mir/instructions caller)) target)))))

(deftest v3-call-liveness-preserves-one-value-across-two-calls
  (let [module {:gmir/version 3
                :gmir/entry 'main
                :gmir/functions
                [{:gmir/name 'inc-one :gmir/arity 1
                  :gmir/instructions
                  [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                   {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 1}
                   {:gmir/op :gmir/add :gmir/dst v2 :gmir/left v0 :gmir/right v1}
                   {:gmir/op :gmir/return :gmir/value v2}]}
                 {:gmir/name 'main :gmir/arity 0
                  :gmir/instructions
                  [{:gmir/op :gmir/constant :gmir/dst v0 :gmir/value 40}
                   {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 1}
                   {:gmir/op :gmir/call :gmir/dst v2
                    :gmir/callee 'inc-one :gmir/arguments [v1]}
                   {:gmir/op :gmir/call :gmir/dst v3
                    :gmir/callee 'inc-one :gmir/arguments [v2]}
                   {:gmir/op :gmir/add :gmir/dst v4 :gmir/left v0 :gmir/right v3}
                   {:gmir/op :gmir/return :gmir/value v4}]}]}]
    (doseq [target mir/targets]
      (let [caller (second (:mir/functions
                            (->> module (mir/select-target target)
                                 mir/allocate-registers)))
            instructions (:mir/instructions caller)]
        (is (= :call-live (:mir/frame-policy caller)) target)
        (is (= 1 (:mir/frame-slots caller)) target)
        (is (= 1 (count (filter #(= :mir/spill-store (:mir/op %)) instructions)))
            target)
        (is (= 1 (count (filter #(= :mir/spill-load (:mir/op %)) instructions)))
            target)
        (is (= 2 (count (filter #(= :mir/call (:mir/op %)) instructions)))
            target)))))

(deftest v3-four-live-entry-arguments-use-parallel-zero-frame-assignment
  (let [arguments [v0 v1 v2 v3]
        sum-instructions
        (vec (concat
              (map-indexed (fn [index value]
                             {:gmir/op :gmir/argument :gmir/dst value
                              :gmir/index index})
                           arguments)
              [{:gmir/op :gmir/add :gmir/dst v4 :gmir/left v0 :gmir/right v1}
               {:gmir/op :gmir/add :gmir/dst v5 :gmir/left v2 :gmir/right v3}
               {:gmir/op :gmir/add :gmir/dst v6 :gmir/left v4 :gmir/right v5}
               {:gmir/op :gmir/return :gmir/value v6}]))
        module {:gmir/version 3
                :gmir/entry 'main
                :gmir/functions
                [{:gmir/name 'sum-four :gmir/arity 4
                  :gmir/instructions sum-instructions}
                 {:gmir/name 'main :gmir/arity 4
                  :gmir/instructions
                  (conj (subvec sum-instructions 0 4)
                        {:gmir/op :gmir/call :gmir/dst v4
                         :gmir/callee 'sum-four :gmir/arguments arguments}
                        {:gmir/op :gmir/return :gmir/value v4})}]}]
    (doseq [target mir/targets]
      (let [[callee caller :as functions]
            (:mir/functions (->> module (mir/select-target target)
                                 mir/allocate-registers))
            expected-inputs (subvec (get mir/call-argument-registers target) 0 4)]
        (doseq [function functions]
          (let [instructions (:mir/instructions function)
                markers (filterv #(= :mir/argument (:mir/op %)) instructions)]
            (is (zero? (:mir/frame-slots function)) [target (:mir/name function)])
            (is (= expected-inputs (mapv :mir/dst markers))
                [target (:mir/name function)])
            (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load}
                                      (:mir/op %))
                          instructions)
                [target (:mir/name function)])))
        (is (= :allocator (:mir/frame-policy callee)) target)
        (is (= :call-live (:mir/frame-policy caller)) target)
        (is (= (if (= :x86-64 target) 3 0)
               (count (filter #(= :mir/move (:mir/op %))
                              (:mir/instructions callee))))
            target)
        (when (= :x86-64 target)
          (is (= [{:mir/op :mir/move :mir/dst :x86-64/rax
                   :mir/src :x86-64/rdi}
                  {:mir/op :mir/move :mir/dst :x86-64/r8
                   :mir/src :x86-64/rcx}
                  {:mir/op :mir/move :mir/dst :x86-64/rcx
                   :mir/src :x86-64/rsi}]
                 (filterv #(= :mir/move (:mir/op %))
                          (:mir/instructions callee)))))))))

(deftest v3-five-live-entry-arguments-spill-only-the-excess-input
  (with-scratch-tier-only
    (let [arguments (mapv gmir/vreg (range 5))
          s01 (gmir/vreg 5)
          s23 (gmir/vreg 6)
          s014 (gmir/vreg 7)
          result (gmir/vreg 8)
          module {:gmir/version 3
                  :gmir/entry 'sum-five
                  :gmir/functions
                  [{:gmir/name 'sum-five :gmir/arity 5
                    :gmir/instructions
                    (vec (concat
                          (map-indexed (fn [index value]
                                         {:gmir/op :gmir/argument :gmir/dst value
                                          :gmir/index index})
                                       arguments)
                          [{:gmir/op :gmir/add :gmir/dst s01
                            :gmir/left (arguments 0) :gmir/right (arguments 1)}
                           {:gmir/op :gmir/add :gmir/dst s23
                            :gmir/left (arguments 2) :gmir/right (arguments 3)}
                           {:gmir/op :gmir/add :gmir/dst s014
                            :gmir/left s01 :gmir/right (arguments 4)}
                           {:gmir/op :gmir/add :gmir/dst result
                            :gmir/left s014 :gmir/right s23}
                           {:gmir/op :gmir/return :gmir/value result}]))}]}]
      (doseq [target mir/targets]
        (let [function (first (:mir/functions
                               (->> module (mir/select-target target)
                                    mir/allocate-registers)))
              instructions (:mir/instructions function)
              fifth-input (nth (get mir/call-argument-registers target) 4)]
          (is (= :allocator (:mir/frame-policy function)) target)
          (is (= 1 (:mir/frame-slots function)) target)
          (is (= [{:mir/op :mir/spill-store :mir/src fifth-input :mir/slot 0}]
                 (filterv #(= :mir/spill-store (:mir/op %)) instructions)) target)
          (let [loads (filterv #(= :mir/spill-load (:mir/op %)) instructions)]
            (is (= 1 (count loads)) target)
            (is (= 0 (:mir/slot (first loads))) target)
            (is (contains? (set (get mir/physical-registers target))
                           (:mir/dst (first loads))) target))
          (is (not-any? gmir/vreg? (tree-seq coll? seq function)) target))))))

(deftest v3-excess-entry-argument-reuses-its-call-live-slot
  (let [arguments (mapv gmir/vreg (range 5))
        call-result (gmir/vreg 5)
        result (gmir/vreg 6)
        module {:gmir/version 3
                :gmir/entry 'main
                :gmir/functions
                [{:gmir/name 'sum-four :gmir/arity 4
                  :gmir/instructions
                  (vec (concat
                        (map-indexed (fn [index value]
                                       {:gmir/op :gmir/argument :gmir/dst value
                                        :gmir/index index})
                                     (subvec arguments 0 4))
                        [{:gmir/op :gmir/add :gmir/dst call-result
                          :gmir/left (arguments 0) :gmir/right (arguments 1)}
                         {:gmir/op :gmir/add :gmir/dst result
                          :gmir/left call-result :gmir/right (arguments 2)}
                         {:gmir/op :gmir/return :gmir/value result}]))}
                 {:gmir/name 'main :gmir/arity 5
                  :gmir/instructions
                  (vec (concat
                        (map-indexed (fn [index value]
                                       {:gmir/op :gmir/argument :gmir/dst value
                                        :gmir/index index})
                                     arguments)
                        [{:gmir/op :gmir/call :gmir/dst call-result
                          :gmir/callee 'sum-four
                          :gmir/arguments (subvec arguments 0 4)}
                         {:gmir/op :gmir/add :gmir/dst result
                          :gmir/left call-result :gmir/right (arguments 4)}
                         {:gmir/op :gmir/return :gmir/value result}]))}]}]
    (doseq [target mir/targets]
      (let [caller (second (:mir/functions
                            (->> module (mir/select-target target)
                                 mir/allocate-registers)))
            instructions (:mir/instructions caller)]
        (is (= :call-live (:mir/frame-policy caller)) target)
        (is (= 1 (:mir/frame-slots caller)) target)
        (is (= [0] (mapv :mir/slot
                         (filter #(= :mir/spill-store (:mir/op %)) instructions)))
            target)
        (is (= [0] (mapv :mir/slot
                         (filter #(= :mir/spill-load (:mir/op %)) instructions)))
            target)))))

(deftest v3-physical-call-contract-fails-closed
  (let [allocated (->> scalar-call-module
                       (mir/select-target :x86-64)
                       mir/allocate-registers)]
    (testing "call functions must declare a closed call frame policy"
      (is (thrown? clojure.lang.ExceptionInfo
                   (mir/validate!
                    (assoc-in allocated [:mir/functions 1 :mir/frame-policy]
                              :allocator)))))
    (testing "physical calls use the exact ABI argument and return registers"
      (let [call-index (first
                        (keep-indexed
                         (fn [index instruction]
                           (when (= :mir/call (:mir/op instruction)) index))
                         (get-in allocated [:mir/functions 1 :mir/instructions])))]
        (is (thrown? clojure.lang.ExceptionInfo
                     (mir/validate!
                      (assoc-in allocated
                                [:mir/functions 1 :mir/instructions call-index
                                 :mir/arguments]
                                [:x86-64/rax]))))))
    (testing "physical entry markers use exact ABI input registers"
      (is (thrown? clojure.lang.ExceptionInfo
                   (mir/validate!
                    (assoc-in allocated
                              [:mir/functions 0 :mir/instructions 0 :mir/dst]
                              :x86-64/rax)))))))

(deftest runtime-call-selection-owns-context-offsets-and-runtime-abi
  (let [program {:gmir/version 1
                 :gmir/instructions
                 [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                  {:gmir/op :gmir/runtime-call :gmir/dst v1
                   :gmir/runtime :vector-count :gmir/arguments [v0]}
                  {:gmir/op :gmir/add :gmir/dst v2
                   :gmir/left v0 :gmir/right v1}
                  {:gmir/op :gmir/return :gmir/value v2}]}]
    (doseq [target mir/targets]
      (let [selected (mir/select-target target program)
            virtual-call (second (:mir/instructions selected))
            allocated (mir/allocate-registers selected)
            call (first (filter #(= :mir/runtime-call (:mir/op %))
                                (:mir/instructions allocated)))]
        (is (= 168 (:mir/context-offset virtual-call)) target)
        (is (= :vector-count (:mir/runtime call)) target)
        (is (= (get mir/return-registers target) (:mir/dst call)) target)
        (is (= (subvec (get mir/runtime-argument-registers target) 0 1)
               (:mir/arguments call)) target)
        (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)) target)
        (testing "the selected context offset cannot drift"
          (is (thrown? clojure.lang.ExceptionInfo
                       (mir/validate! (update-in allocated [:mir/instructions]
                                                 (fn [instructions]
                                                   (mapv #(if (= :mir/runtime-call
                                                                  (:mir/op %))
                                                            (assoc % :mir/context-offset 176)
                                                            %)
                                                         instructions)))))
              target))))))

(deftest immutable-data-address-selection-preserves-content
  (let [program {:gmir/version 1
                 :gmir/instructions
                 [{:gmir/op :gmir/data-address :gmir/dst v0
                   :gmir/content "hello😀"}
                  {:gmir/op :gmir/return :gmir/value v0}]}]
    (doseq [target mir/targets]
      (let [selected (mir/select-target target program)
            allocated (mir/allocate-registers selected)
            literal (first (:mir/instructions allocated))]
        (is (= :mir/data-address (:mir/op literal)) target)
        (is (= "hello😀" (:mir/content literal)) target)
        (is (= (name target) (namespace (:mir/dst literal))) target)))))

(deftest v3-runtime-call-preserves-values-live-across-the-host-boundary
  (let [module {:gmir/version 3
                :gmir/entry 'main
                :gmir/functions
                [{:gmir/name 'main :gmir/arity 1
                  :gmir/instructions
                  [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                   {:gmir/op :gmir/runtime-call :gmir/dst v1
                    :gmir/runtime :vector-count :gmir/arguments [v0]}
                   {:gmir/op :gmir/add :gmir/dst v2
                    :gmir/left v0 :gmir/right v1}
                   {:gmir/op :gmir/return :gmir/value v2}]}]}]
    (doseq [target mir/targets]
      (let [function (->> module
                          (mir/select-target target)
                          mir/allocate-registers
                          :mir/functions
                          first)
            instructions (:mir/instructions function)]
        (is (= :call-live (:mir/frame-policy function)) target)
        (is (= 1 (:mir/frame-slots function)) target)
        (is (= [0] (mapv :mir/slot
                         (filter #(= :mir/spill-store (:mir/op %))
                                 instructions))) target)
        (is (= [0] (mapv :mir/slot
                         (filter #(= :mir/spill-load (:mir/op %))
                                 instructions))) target)))))

(deftest v2-control-flow-validates-with-host-calls
  (doseq [target mir/targets
          call [{:gmir/op :gmir/runtime-call :gmir/dst v1
                 :gmir/runtime :pair-first :gmir/arguments [v0]}
                {:gmir/op :gmir/capability-call :gmir/dst v1
                 :gmir/capability 7 :gmir/kind :i64
                 :gmir/arguments [v0]}]]
    (let [then-label :kotoba.gmir.label/then
          end-label :kotoba.gmir.label/end
          program {:gmir/version 2
                   :gmir/instructions
                   [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                    call
                    {:gmir/op :gmir/branch-zero :gmir/test v1
                     :gmir/target then-label}
                    {:gmir/op :gmir/jump :gmir/target end-label}
                    {:gmir/op :gmir/label :gmir/id then-label}
                    {:gmir/op :gmir/label :gmir/id end-label}
                    {:gmir/op :gmir/return :gmir/value v0}]}
          selected (mir/select-target target program)
          allocated (mir/allocate-registers selected)]
      (is (= 2 (:mir/version selected)) [target (:gmir/op call)])
      (is (= :physical (:mir/registers allocated)) [target (:gmir/op call)])
      (is (some :mir/context-offset (:mir/instructions allocated))
          [target (:gmir/op call)]))))

(deftest capability-call-selection-owns-kind-specific-context-and-abi
  (doseq [target mir/targets
          kind (keys gmir/capability-kinds)]
    (let [program {:gmir/version 1
                   :gmir/instructions
                   [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                    {:gmir/op :gmir/capability-call :gmir/dst v1
                     :gmir/capability 7 :gmir/kind kind
                     :gmir/arguments [v0]}
                    {:gmir/op :gmir/add :gmir/dst v2
                     :gmir/left v0 :gmir/right v1}
                    {:gmir/op :gmir/return :gmir/value v2}]}
          selected (mir/select-target target program)
          allocated (mir/allocate-registers selected)
          call (first (filter #(= :mir/capability-call (:mir/op %))
                              (:mir/instructions allocated)))]
      (is (= (get mir/capability-context-offsets kind)
             (:mir/context-offset call)) [target kind])
      (is (= (get-in mir/capability-argument-registers [target kind])
             (:mir/arguments call)) [target kind])
      (is (= 7 (:mir/capability call)) [target kind])
      (is (= kind (:mir/kind call)) [target kind])
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)) [target kind])
      (is (thrown? clojure.lang.ExceptionInfo
                   (mir/validate!
                    (update-in allocated [:mir/instructions]
                               (fn [instructions]
                                 (mapv #(if (= :mir/capability-call (:mir/op %))
                                          (assoc % :mir/context-offset 40)
                                          %)
                                       instructions)))))
          [target kind]))))

;; ── The tiers themselves ─────────────────────────────────────────────────────

(deftest allocator-pool-offers-the-leaf-tier-only-to-functions-that-call-nothing
  (doseq [target mir/targets]
    (let [leaf (mir/allocator-pool target {:leaf? true})
          calling (mir/allocator-pool target {:leaf? false})]
      (is (= (count (distinct leaf)) (count leaf)) target)
      (is (= (count (distinct calling)) (count calling)) target)
      (is (= (vec (concat (get mir/physical-registers target)
                          (get mir/leaf-registers target)
                          (get mir/preserved-registers target)))
             leaf) target)
      (is (empty? (filter (set (get mir/leaf-registers target)) calling)) target)
      ;; The scratch tier comes first so a function small enough to stay inside
      ;; it names no preserved register and its frame saves nothing.
      (is (= (get mir/physical-registers target)
             (subvec leaf 0 (count (get mir/physical-registers target))))
          target))))

(deftest a-tier-register-is-never-two-things-at-once
  (doseq [target mir/targets]
    (let [scratch (set (get mir/physical-registers target))
          leaf (set (get mir/leaf-registers target))
          preserved (set (get mir/preserved-registers target))]
      (is (empty? (clojure.set/intersection scratch leaf)) target)
      (is (empty? (clojure.set/intersection scratch preserved)) target)
      (is (empty? (clojure.set/intersection leaf preserved)) target)
      ;; A callee-saved register the caller also passes arguments in would be
      ;; saved and clobbered by the same function.
      (is (empty? (clojure.set/intersection
                   preserved (set (get mir/call-argument-registers target))))
          target))))

(deftest eleven-live-values-fit-without-touching-the-stack
  (let [registers (mapv gmir/vreg (range 11))
        program {:gmir/version 1
                 :gmir/instructions
                 (vec (concat
                       (map-indexed (fn [index register]
                                      {:gmir/op :gmir/constant :gmir/dst register
                                       :gmir/value index})
                                    (subvec registers 0 6))
                       [{:gmir/op :gmir/add :gmir/dst (registers 6)
                         :gmir/left (registers 0) :gmir/right (registers 1)}
                        {:gmir/op :gmir/add :gmir/dst (registers 7)
                         :gmir/left (registers 2) :gmir/right (registers 3)}
                        {:gmir/op :gmir/add :gmir/dst (registers 8)
                         :gmir/left (registers 4) :gmir/right (registers 5)}
                        {:gmir/op :gmir/add :gmir/dst (registers 9)
                         :gmir/left (registers 6) :gmir/right (registers 7)}
                        {:gmir/op :gmir/add :gmir/dst (registers 10)
                         :gmir/left (registers 9) :gmir/right (registers 8)}
                        {:gmir/op :gmir/return :gmir/value (registers 10)}]))}
        allocated (->> program (mir/select-target :x86-64) mir/allocate-registers)]
    ;; The same program the exhaustion test uses. Under the scratch tier alone
    ;; it takes eleven stack slots; with the tiers on offer it takes none.
    (is (zero? (:mir/frame-slots allocated)))
    (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load} (:mir/op %))
                  (:mir/instructions allocated)))
    (is (= allocated
           (->> program (mir/select-target :x86-64) mir/allocate-registers)))))

(deftest five-live-entry-arguments-now-all-arrive-in-registers
  (let [arguments (mapv gmir/vreg (range 5))
        [s01 s23 s014 result] (map gmir/vreg (range 5 9))
        module {:gmir/version 3
                :gmir/entry 'sum-five
                :gmir/functions
                [{:gmir/name 'sum-five :gmir/arity 5
                  :gmir/instructions
                  (vec (concat
                        (map-indexed (fn [index value]
                                       {:gmir/op :gmir/argument :gmir/dst value
                                        :gmir/index index})
                                     arguments)
                        [{:gmir/op :gmir/add :gmir/dst s01
                          :gmir/left (arguments 0) :gmir/right (arguments 1)}
                         {:gmir/op :gmir/add :gmir/dst s23
                          :gmir/left (arguments 2) :gmir/right (arguments 3)}
                         {:gmir/op :gmir/add :gmir/dst s014
                          :gmir/left s01 :gmir/right (arguments 4)}
                         {:gmir/op :gmir/add :gmir/dst result
                          :gmir/left s014 :gmir/right s23}
                         {:gmir/op :gmir/return :gmir/value result}]))}]}]
    (doseq [target mir/targets]
      (let [function (first (:mir/functions
                             (->> module (mir/select-target target)
                                  mir/allocate-registers)))]
        (is (= :allocator (:mir/frame-policy function)) target)
        (is (zero? (:mir/frame-slots function)) target)
        (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load}
                                  (:mir/op %))
                      (:mir/instructions function)) target)))))

(deftest saved-registers-names-exactly-what-the-body-uses
  (doseq [target mir/targets]
    (let [preserved (get mir/preserved-registers target)
          registers (mapv gmir/vreg (range 11))
          program {:gmir/version 1
                   :gmir/instructions
                   (vec (concat
                         (map-indexed (fn [index register]
                                        {:gmir/op :gmir/constant
                                         :gmir/dst register :gmir/value index})
                                      (subvec registers 0 6))
                         [{:gmir/op :gmir/add :gmir/dst (registers 6)
                           :gmir/left (registers 0) :gmir/right (registers 1)}
                          {:gmir/op :gmir/add :gmir/dst (registers 7)
                           :gmir/left (registers 2) :gmir/right (registers 3)}
                          {:gmir/op :gmir/add :gmir/dst (registers 8)
                           :gmir/left (registers 4) :gmir/right (registers 5)}
                          {:gmir/op :gmir/add :gmir/dst (registers 9)
                           :gmir/left (registers 6) :gmir/right (registers 7)}
                          {:gmir/op :gmir/add :gmir/dst (registers 10)
                           :gmir/left (registers 9) :gmir/right (registers 8)}
                          {:gmir/op :gmir/return :gmir/value (registers 10)}]))}
          instructions (:mir/instructions
                        (->> program (mir/select-target target)
                             mir/allocate-registers))
          named (set (filter (set preserved) (tree-seq coll? seq instructions)))]
      (is (= (filterv named preserved) (mir/saved-registers target instructions))
          target)
      ;; Reported in pool order, so a frame that saves them in order and
      ;; restores them in reverse never has to sort anything.
      (is (= (mir/saved-registers target instructions)
             (filterv (set (mir/saved-registers target instructions)) preserved))
          target)
      (is (empty? (mir/saved-registers target [])) target))))

(deftest a-body-that-stays-in-the-scratch-tier-saves-nothing
  (doseq [target mir/targets]
    (let [program {:gmir/version 1
                   :gmir/instructions
                   [{:gmir/op :gmir/constant :gmir/dst v0 :gmir/value 1}
                    {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 2}
                    {:gmir/op :gmir/add :gmir/dst v2 :gmir/left v0 :gmir/right v1}
                    {:gmir/op :gmir/return :gmir/value v2}]}
          instructions (:mir/instructions
                        (->> program (mir/select-target target)
                             mir/allocate-registers))]
      (is (empty? (mir/saved-registers target instructions)) target))))
