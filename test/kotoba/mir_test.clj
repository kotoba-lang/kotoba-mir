(ns kotoba.mir-test
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.gmir :as gmir]
            [kotoba.mir :as mir]))

(def v0 (gmir/vreg 0))
(def v1 (gmir/vreg 1))
(def v2 (gmir/vreg 2))
(def v3 (gmir/vreg 3))
(def v4 (gmir/vreg 4))

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

(deftest acyclic-multi-phi-join-coalesces-to-direct-edge-moves
  (doseq [target mir/targets]
    (let [allocated (->> dual-phi-program (mir/select-target target) mir/allocate-registers)
          instructions (:mir/instructions allocated)]
      (is (zero? (:mir/frame-slots allocated)))
      (is (= 2 (count (filter #(= :mir/move (:mir/op %)) instructions))))
      (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load} (:mir/op %))
                    instructions))
      (is (= allocated
             (->> dual-phi-program (mir/select-target target) mir/allocate-registers))))))

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

(deftest v3-call-arguments-are-loaded-in-parallel-from-stable-frame-slots
  (let [args (mapv gmir/vreg (range 5))
        result (gmir/vreg 5)
        module {:gmir/version 3
                :gmir/entry 'main
                :gmir/functions
                [{:gmir/name 'callee :gmir/arity 5
                  :gmir/instructions
                  [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                   {:gmir/op :gmir/return :gmir/value v0}]}
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
            loads (subvec instructions (- call-index 5) call-index)]
        (is (= :all-vregs (:mir/frame-policy caller)) target)
        (is (= (get mir/call-argument-registers target)
               (mapv :mir/dst loads)) target)
        (is (= (vec (range 5)) (mapv :mir/slot loads)) target)
        (is (every? #(= :mir/spill-load (:mir/op %)) loads) target)))))

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
                                [:x86-64/rax]))))))))
