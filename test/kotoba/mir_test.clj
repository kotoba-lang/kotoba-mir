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

(deftest physical-register-classification-rejects-integer-immediates
  (let [physical-register? @#'kotoba.mir/physical-register?]
    (doseq [target mir/targets]
      (is (false? (physical-register? target 0N)) target)
      (is (true? (physical-register? target
                                     (first (get mir/physical-registers target))))
          target))))

(deftest latency-aware-scheduling-fills-an-integer-multiply-dependency-gap
  (let [schedule @#'kotoba.mir/schedule-instructions
        [a b c d x independent dependent result] (map gmir/vreg (range 8))
        instructions
        [{:mir/op :mir/multiply :mir/dst x :mir/left a :mir/right b}
         {:mir/op :mir/multiply :mir/dst dependent :mir/left x :mir/right c}
         {:mir/op :mir/add :mir/dst independent :mir/left c :mir/right d}
         {:mir/op :mir/add :mir/dst result :mir/left dependent
          :mir/right independent}]
        expected [x independent dependent result]]
    (doseq [target mir/targets]
      (let [scheduled (schedule target instructions)]
        (is (= expected (mapv :mir/dst scheduled)) target)
        (is (= scheduled (schedule target instructions))
            [target :deterministic])))))

(deftest instruction-scheduling-keeps-trapping-and-effectful-barriers-fixed
  (let [schedule @#'kotoba.mir/schedule-instructions
        [a b c d x q y called z] (map gmir/vreg (range 9))
        barrier-ops [:mir/quotient :mir/kernel-load-u8 :mir/call
                     :mir/runtime-call :mir/capability-call
                     :mir/branch-zero :mir/branch-nonzero :mir/return]]
    (doseq [target mir/targets
            barrier-op barrier-ops]
      (let [barrier (case barrier-op
                      :mir/quotient
                      {:mir/op barrier-op :mir/dst q :mir/left x :mir/right c}
                      :mir/kernel-load-u8
                      {:mir/op barrier-op :mir/dst q :mir/base a :mir/length b
                       :mir/index c :mir/maximum 512}
                      :mir/call
                      {:mir/op barrier-op :mir/dst called :mir/callee 'callee
                       :mir/arguments [x]}
                      :mir/runtime-call
                      {:mir/op barrier-op :mir/dst called :mir/runtime :print
                       :mir/context-offset 0 :mir/arguments [x]}
                      :mir/capability-call
                      {:mir/op barrier-op :mir/dst called :mir/capability :test
                       :mir/kind :i64 :mir/context-offset 0 :mir/arguments [x]}
                      :mir/branch-zero
                      {:mir/op barrier-op :mir/test x :mir/target :done}
                      :mir/branch-nonzero
                      {:mir/op barrier-op :mir/test x :mir/target :done}
                      :mir/return
                      {:mir/op barrier-op :mir/value x})
            instructions
            [{:mir/op :mir/multiply :mir/dst x :mir/left a :mir/right b}
             barrier
             {:mir/op :mir/add :mir/dst y :mir/left c :mir/right d}
             {:mir/op :mir/add :mir/dst z :mir/left y :mir/right d}]
            scheduled (schedule target instructions)]
        (is (= barrier (nth scheduled 1)) [target barrier-op])
        (is (= (count instructions) (count scheduled)) [target barrier-op])))))

(deftest aarch64-scheduling-preserves-existing-fused-multiply-candidates
  (let [schedule @#'kotoba.mir/schedule-instructions
        [a b c d product fused independent result] (map gmir/vreg (range 8))
        instructions
        [{:mir/op :mir/multiply :mir/dst product :mir/left a :mir/right b}
         {:mir/op :mir/add :mir/dst fused :mir/left product :mir/right c}
         {:mir/op :mir/add :mir/dst independent :mir/left c :mir/right d}
         {:mir/op :mir/add :mir/dst result :mir/left fused
          :mir/right independent}]
        scheduled (schedule :aarch64 instructions)]
    (is (= [product fused independent result] (mapv :mir/dst scheduled)))
    (is (= scheduled (schedule :aarch64 instructions)))))

(deftest per-basic-block-scheduling-reorders-only-within-barrier-bounded-segments
  (let [schedule @#'kotoba.mir/schedule-instructions
        [a b c d x dependent independent] (map gmir/vreg (range 7))
        instructions
        [{:mir/op :mir/multiply :mir/dst x :mir/left a :mir/right b}
         {:mir/op :mir/multiply :mir/dst dependent :mir/left x :mir/right c}
         {:mir/op :mir/add :mir/dst independent :mir/left c :mir/right d}
         {:mir/op :mir/branch-zero :mir/test independent :mir/target :done}
         {:mir/op :mir/label :mir/id :done}
         {:mir/op :mir/return :mir/value dependent}]
        expected-pre-branch [x independent dependent]]
    (doseq [target mir/targets]
      (let [scheduled (schedule target instructions)]
        (is (= expected-pre-branch (mapv :mir/dst (subvec scheduled 0 3))) target)
        (is (= (subvec instructions 3) (subvec scheduled 3)) target)))))

(deftest integer-schedule-validation-accepts-dependency-respecting-reorder
  (let [valid? @#'kotoba.mir/valid-scheduled-segment?
        schedule-indexes @#'kotoba.mir/schedule-integer-segment-indices
        [a b c d x independent dependent result] (map gmir/vreg (range 8))
        instructions
        [{:mir/op :mir/multiply :mir/dst x :mir/left a :mir/right b}
         {:mir/op :mir/multiply :mir/dst dependent :mir/left x :mir/right c}
         {:mir/op :mir/add :mir/dst independent :mir/left c :mir/right d}
         {:mir/op :mir/add :mir/dst result :mir/left dependent
          :mir/right independent}]
        scheduled-indexes (schedule-indexes :x86-64 instructions)]
    (doseq [target mir/targets]
      (is (valid? target instructions (schedule-indexes target instructions)) target))
    (is (= [0 2 1 3] scheduled-indexes))))

(deftest post-allocation-scheduling-preserves-physical-register-hazards
  (let [schedule-indexes @#'kotoba.mir/schedule-integer-segment-indices
        valid? @#'kotoba.mir/valid-scheduled-segment?
        [r0 r1 r2 r3 r4 r5 r6 r7] (map #(keyword "aarch64" (str "x" %))
                                        (range 8))
        ;; The multiply chain makes the later r0 definition attractive to the
        ;; scheduler. It must still remain after the earlier r0 read (WAR).
        war [{:mir/op :mir/add :mir/dst r2 :mir/left r0 :mir/right r1}
             {:mir/op :mir/add :mir/dst r3 :mir/left r4 :mir/right r5}
             {:mir/op :mir/multiply :mir/dst r0 :mir/left r4 :mir/right r5}
             {:mir/op :mir/multiply :mir/dst r6 :mir/left r0 :mir/right r7}]
        ;; The first r0 definition has no reader, but must remain before its
        ;; replacement or it could move after it and change the final read.
        waw [{:mir/op :mir/add :mir/dst r0 :mir/left r1 :mir/right r2}
             {:mir/op :mir/add :mir/dst r3 :mir/left r4 :mir/right r5}
             {:mir/op :mir/multiply :mir/dst r0 :mir/left r4 :mir/right r5}
             {:mir/op :mir/multiply :mir/dst r6 :mir/left r0 :mir/right r7}]]
    (doseq [instructions [war waw]]
      (let [order (schedule-indexes :aarch64 instructions)
            positions (zipmap order (range))]
        (is (< (positions 0) (positions 2)) [instructions order])
        (is (valid? :aarch64 instructions order) [instructions order])
        (is (not (valid? :aarch64 instructions [2 0 1 3]))
            [instructions :unsafe-order-must-be-rejected])))))

(deftest integer-schedule-validation-rejects-dependency-violating-order
  (let [valid? @#'kotoba.mir/valid-scheduled-segment?
        [a b c d x dependent independent result] (map gmir/vreg (range 8))
        instructions
        [{:mir/op :mir/multiply :mir/dst x :mir/left a :mir/right b}
         {:mir/op :mir/multiply :mir/dst dependent :mir/left x :mir/right c}
         {:mir/op :mir/add :mir/dst independent :mir/left c :mir/right d}
         {:mir/op :mir/add :mir/dst result :mir/left dependent
          :mir/right independent}]
        violating [2 1 0 3]]
    (doseq [target mir/targets]
      (is (not (valid? target instructions violating)) target))))

(deftest integer-schedule-validation-preserves-duplicate-instruction-identities
  (let [valid? @#'kotoba.mir/valid-scheduled-segment?
        register (first (:x86-64 mir/leaf-registers))
        duplicate {:mir/op :mir/add :mir/dst register
                   :mir/left register :mir/right register}
        instructions [duplicate duplicate]]
    ;; The instruction values are structurally equal, but their original
    ;; positions remain distinct schedule identities.
    (is (valid? :x86-64 instructions [0 1]))
    (is (not (valid? :x86-64 instructions [0 0])))
    (is (not (valid? :x86-64 instructions [1 1])))))

(deftest modeled-completion-score-improves-on-multiply-dependency-gap
  (let [sum-times @#'kotoba.mir/segment-sum-completion-times
        valid? @#'kotoba.mir/valid-scheduled-segment?
        [a b c d x independent dependent result] (map gmir/vreg (range 8))
        instructions
        [{:mir/op :mir/multiply :mir/dst x :mir/left a :mir/right b}
         {:mir/op :mir/multiply :mir/dst dependent :mir/left x :mir/right c}
         {:mir/op :mir/add :mir/dst independent :mir/left c :mir/right d}
         {:mir/op :mir/add :mir/dst result :mir/left dependent
          :mir/right independent}]]
    (doseq [target mir/targets]
      (let [program-order [0 1 2 3]
            latency-filling-order [0 2 1 3]
            before-sum (sum-times target instructions program-order)
            after-sum (sum-times target instructions latency-filling-order)]
        (is (valid? target instructions program-order) [target :program-order])
        (is (valid? target instructions latency-filling-order)
            [target :latency-filling-order])
        (is (< after-sum before-sum) [target :sum-completion-times])
        (is (= 21 before-sum) [target :program-order-sum])
        (is (= 18 after-sum) [target :scheduled-sum])))))

(deftest scheduling-after-allocation-keeps-spill-stores-at-definitions
  (with-scratch-tier-only
    (let [[a b c d x1 x2 x3 then-y else-y join result] (map gmir/vreg (range 11))
          program
          {:gmir/version 2
           :gmir/instructions
           [{:gmir/op :gmir/constant :gmir/dst a :gmir/value 1}
            {:gmir/op :gmir/constant :gmir/dst b :gmir/value 2}
            {:gmir/op :gmir/constant :gmir/dst c :gmir/value 3}
            {:gmir/op :gmir/constant :gmir/dst d :gmir/value 4}
            {:gmir/op :gmir/branch-zero :gmir/test a :gmir/target :test.label/else}
            {:gmir/op :gmir/label :gmir/id :test.label/then}
            {:gmir/op :gmir/add :gmir/dst x1 :gmir/left c :gmir/right d}
            {:gmir/op :gmir/add :gmir/dst x2 :gmir/left c :gmir/right d}
            {:gmir/op :gmir/add :gmir/dst x3 :gmir/left x1 :gmir/right x2}
            {:gmir/op :gmir/add :gmir/dst then-y :gmir/left x3 :gmir/right d}
            {:gmir/op :gmir/label :gmir/id :test.label/then-exit}
            {:gmir/op :gmir/jump :gmir/target :test.label/join}
            {:gmir/op :gmir/label :gmir/id :test.label/else}
            {:gmir/op :gmir/add :gmir/dst else-y :gmir/left b :gmir/right c}
            {:gmir/op :gmir/label :gmir/id :test.label/else-exit}
            {:gmir/op :gmir/jump :gmir/target :test.label/join}
            {:gmir/op :gmir/label :gmir/id :test.label/join}
            {:gmir/op :gmir/phi :gmir/dst join
             :gmir/incomings [{:gmir/predecessor :test.label/then-exit :gmir/value then-y}
                              {:gmir/predecessor :test.label/else-exit :gmir/value else-y}]}
            {:gmir/op :gmir/add :gmir/dst result :gmir/left join :gmir/right d}
            {:gmir/op :gmir/return :gmir/value result}]}
          instructions (:mir/instructions
                        (->> program (mir/select-target :x86-64)
                             mir/allocate-registers))
          numbered (vec (map-indexed vector instructions))
          stores (filter (fn [[_ i]] (= :mir/spill-store (:mir/op i))) numbered)]
      (is (seq stores))
      (doseq [[position store] stores]
        (is (= (:mir/src store) (:mir/dst (nth instructions (dec position))))
            (str "store at " position " follows its definition on CFG pressure"))))))

(deftest scheduling-preserves-phi-transport-coalescing-groups
  (let [[a b then-v else-v join] (map gmir/vreg (range 5))
        program {:gmir/version 2
                 :gmir/instructions
                 [{:gmir/op :gmir/constant :gmir/dst a :gmir/value 1}
                  {:gmir/op :gmir/constant :gmir/dst b :gmir/value 2}
                  {:gmir/op :gmir/branch-zero :gmir/test a
                   :gmir/target :test.label/else}
                  {:gmir/op :gmir/label :gmir/id :test.label/then}
                  {:gmir/op :gmir/add :gmir/dst then-v :gmir/left a :gmir/right b}
                  {:gmir/op :gmir/label :gmir/id :test.label/then-exit}
                  {:gmir/op :gmir/jump :gmir/target :test.label/join}
                  {:gmir/op :gmir/label :gmir/id :test.label/else}
                  {:gmir/op :gmir/add :gmir/dst else-v :gmir/left b :gmir/right a}
                  {:gmir/op :gmir/label :gmir/id :test.label/else-exit}
                  {:gmir/op :gmir/jump :gmir/target :test.label/join}
                  {:gmir/op :gmir/label :gmir/id :test.label/join}
                  {:gmir/op :gmir/phi :gmir/dst join
                   :gmir/incomings
                   [{:gmir/predecessor :test.label/then-exit :gmir/value then-v}
                    {:gmir/predecessor :test.label/else-exit :gmir/value else-v}]}
                  {:gmir/op :gmir/return :gmir/value join}]}
        allocated (:mir/instructions
                   (->> program (mir/select-target :x86-64) mir/allocate-registers))]
    (is (not (some #(= :mir/merge-store (:mir/op %)) allocated))
        "edge merge stores coalesce to moves on CFG programs")
    (is (some #(= :mir/move (:mir/op %)) allocated))))

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

(deftest aarch64-vmir-fuses-unique-zero-equality-branch-before-allocation
  (let [module {:gmir/version 3 :gmir/entry 'kernel
                :gmir/functions
                [{:gmir/name 'kernel :gmir/arity 1
                  :gmir/instructions
                  [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
                   {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 0}
                   {:gmir/op :gmir/equal :gmir/dst v2
                    :gmir/left v0 :gmir/right v1}
                   {:gmir/op :gmir/branch-zero :gmir/test v2
                    :gmir/target :test.label/nonzero}
                   {:gmir/op :gmir/return :gmir/value v0}
                   {:gmir/op :gmir/label :gmir/id :test.label/nonzero}
                   {:gmir/op :gmir/return :gmir/value v0}]}]}
        expected {:mir/op :mir/branch-nonzero :mir/test v0
                  :mir/target :test.label/nonzero}
        arm (mir/select-target :aarch64 module)
        arm-instructions (get-in arm [:mir/functions 0 :mir/instructions])
        allocated (mir/allocate-registers arm)
        physical-instructions (get-in allocated [:mir/functions 0 :mir/instructions])
        x86-instructions (get-in (mir/select-target :x86-64 module)
                                 [:mir/functions 0 :mir/instructions])]
    (is (= expected (second arm-instructions)))
    (is (= 5 (count arm-instructions))
        "zero and equality definitions are removed, not merely ignored later")
    (is (not-any? #(contains? #{:mir/constant :mir/equal} (:mir/op %))
                  arm-instructions))
    (is (= :mir/branch-nonzero (:mir/op (second physical-instructions))))
    (is (keyword? (:mir/test (second physical-instructions))))
    (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)))
    (is (= [:mir/argument :mir/constant :mir/equal :mir/branch-zero
            :mir/return :mir/label :mir/return]
           (mapv :mir/op x86-instructions))
        "x86 selection remains byte-path compatible with its TEST/JZ lowering")
    (let [reversed (assoc-in module [:gmir/functions 0 :gmir/instructions 2]
                             {:gmir/op :gmir/equal :gmir/dst v2
                              :gmir/left v1 :gmir/right v0})]
      (is (= expected
             (get-in (mir/select-target :aarch64 reversed)
                     [:mir/functions 0 :mir/instructions 1]))
          "either equality operand orientation denotes the same fusion"))))

(deftest aarch64-vmir-zero-equality-fusion-requires-global-unique-uses
  (let [fuse @#'kotoba.mir/aarch64-fuse-zero-equality-branches
        zero {:mir/op :mir/constant :mir/dst v1 :mir/value 0}
        equal {:mir/op :mir/equal :mir/dst v2 :mir/left v0 :mir/right v1}
        branch {:mir/op :mir/branch-zero :mir/test v2
                :mir/target :test.label/nonzero}
        fused [{:mir/op :mir/branch-nonzero :mir/test v0
                :mir/target :test.label/nonzero}]
        label {:mir/op :mir/label :mir/id :test.label/nonzero}]
    (is (= fused (fuse :aarch64 [zero equal branch])))
    (is (= [zero equal branch] (fuse :x86-64 [zero equal branch])))
    (doseq [[why instructions]
            [["zero is reused"
              [zero equal branch
               {:mir/op :mir/add :mir/dst v3 :mir/left v0 :mir/right v1}]]
             ["equality result is reused"
              [zero equal branch
               {:mir/op :mir/add :mir/dst v3 :mir/left v0 :mir/right v2}]]
             ["phi incoming is a global use"
              [zero equal branch label
               {:mir/op :mir/phi :mir/dst v3
                :mir/incomings [{:mir/predecessor :test.label/nonzero
                                 :mir/value v1}]}]]
             ["equality result reused by phi is global"
              [zero equal branch label
               {:mir/op :mir/phi :mir/dst v3
                :mir/incomings [{:mir/predecessor :test.label/nonzero
                                 :mir/value v2}]}]]
             ["the same zero occupies both equality operands"
              [zero (assoc equal :mir/left v1 :mir/right v1) branch]]
             ["constant is nonzero" [(assoc zero :mir/value 1) equal branch]]
             ["branch reads another value" [zero equal (assoc branch :mir/test v3)]]
             ["comparison is not equality" [zero (assoc equal :mir/op :mir/less-than)
                                               branch]]
             ["a label interrupts adjacency" [zero equal label branch]]
             ["definition order is reversed" [equal zero branch]]
             ["operand aliases result" [zero (assoc equal :mir/left v2) branch]]]]
      (is (= instructions (fuse :aarch64 instructions)) why))))

(deftest branch-nonzero-schema-sources-cfg-and-target-closure
  (let [sources @#'kotoba.mir/instruction-sources
        last-uses @#'kotoba.mir/cfg-last-uses
        back-edge? @#'kotoba.mir/back-edge?
        branch {:mir/op :mir/branch-nonzero :mir/test v0
                :mir/target :test.label/loop}
        instructions [{:mir/op :mir/argument :mir/dst v0 :mir/index 0}
                      {:mir/op :mir/label :mir/id :test.label/loop}
                      branch]
        module {:mir/version 3 :mir/target :aarch64 :mir/registers :virtual
                :mir/entry 'kernel
                :mir/functions [{:mir/name 'kernel :mir/arity 1
                                 :mir/instructions instructions}]}]
    (is (= [v0] (vec (sources branch))))
    (is (= 2 (get (last-uses instructions) v0)))
    (is (true? (back-edge? instructions)))
    (is (= module (mir/validate! module)))
    (is (thrown? clojure.lang.ExceptionInfo
                 (mir/validate! (assoc module :mir/target :x86-64))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (mir/validate!
                  (assoc-in module [:mir/functions 0 :mir/instructions 2]
                            (assoc branch :extra true)))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (mir/validate!
                  (assoc-in module [:mir/functions 0 :mir/instructions 2]
                            (dissoc branch :mir/test)))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (mir/validate!
                  (assoc-in module [:mir/functions 0 :mir/instructions 2 :mir/target]
                            :test.label/missing))))
    (doseq [version [1 2]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (mir/validate! {:mir/version version :mir/target :aarch64
                                   :mir/registers :physical :mir/frame-slots 0
                                   :mir/instructions
                                   [{:mir/op :mir/label :mir/id :test.label/loop}
                                    {:mir/op :mir/branch-nonzero
                                     :mir/test :aarch64/x0
                                     :mir/target :test.label/loop}]}))
          (str "branch-nonzero is derived only in v3, not public v" version)))))

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
      (is (= 2 (:mir/frame-slots allocated))
          "six live f64 constants on four scratch registers spill two, not eleven")
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
      (is (= 2 (:mir/frame-slots allocated))
          "six live constants on four scratch registers spill two, not every vreg")
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
          instructions (:mir/instructions allocated)
          spill-slots (into #{} (keep :mir/slot
                                     (filter #(contains? #{:mir/spill-store
                                                           :mir/spill-load}
                                                         (:mir/op %))
                                             instructions)))]
      (is (= 2 (:mir/frame-slots allocated))
          "pressure spills two live constants; the join does not add a slot")
      (is (= #{0 1} spill-slots)
          "phi coalescing reuses edge moves instead of a third merge slot")
      (is (some #(= :mir/move (:mir/op %)) instructions)
          "the no-spill join still coalesces to a move")
      (is (not-any? #(= :mir/phi (:mir/op %)) instructions)))))

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

(def call-branch-module
  "The same caller as scalar-call-module, with one `if` around the add. Only
  the allocation path differs: labels used to send the body to all-vreg."
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
      {:gmir/op :gmir/branch-zero :gmir/test v0 :gmir/target :test.label/else}
      {:gmir/op :gmir/label :gmir/id :test.label/then}
      {:gmir/op :gmir/add :gmir/dst v3 :gmir/left v2 :gmir/right v1}
      {:gmir/op :gmir/label :gmir/id :test.label/then-exit}
      {:gmir/op :gmir/jump :gmir/target :test.label/join}
      {:gmir/op :gmir/label :gmir/id :test.label/else}
      {:gmir/op :gmir/constant :gmir/dst v4 :gmir/value 0}
      {:gmir/op :gmir/label :gmir/id :test.label/else-exit}
      {:gmir/op :gmir/jump :gmir/target :test.label/join}
      {:gmir/op :gmir/label :gmir/id :test.label/join}
      {:gmir/op :gmir/phi :gmir/dst v5
       :gmir/incomings
       [{:gmir/predecessor :test.label/then-exit :gmir/value v3}
        {:gmir/predecessor :test.label/else-exit :gmir/value v4}]}
      {:gmir/op :gmir/return :gmir/value v5}]}]})

(defn- value-ops-unbacked-by-store
  [instructions]
  (let [value-ops #{:mir/argument :mir/constant :mir/add :mir/call
                    :mir/runtime-call :mir/capability-call}]
    (keep-indexed
     (fn [index instruction]
       (when (and (contains? value-ops (:mir/op instruction))
                  (let [store (get instructions (inc index))]
                    (not (and (= :mir/spill-store (:mir/op store))
                              (= (:mir/dst instruction) (:mir/src store))))))
         instruction))
     instructions)))

(deftest v3-call-with-control-flow-uses-the-linear-scanner
  (doseq [target mir/targets]
    (let [allocated (->> call-branch-module
                         (mir/select-target target)
                         mir/allocate-registers)
          [callee caller] (:mir/functions allocated)
          instructions (:mir/instructions caller)
          call (first (filter #(= :mir/call (:mir/op %)) instructions))]
      (is (= :allocator (:mir/frame-policy callee)) target)
      (is (= :call-live (:mir/frame-policy caller)) target)
      (is (< (:mir/frame-slots caller) 6) target)
      (is (seq (value-ops-unbacked-by-store instructions))
          (str target " must not take the all-vreg path (every value stored)"))
      (is (= (get mir/return-registers target) (:mir/dst call)) target)
      (is (= [(first (get mir/call-argument-registers target))]
             (:mir/arguments call)) target)
      (is (seq (mir/saved-registers target instructions))
          (str target " keeps a live-across value in the preserved tier"))
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)) target)
      (is (= allocated (->> call-branch-module
                            (mir/select-target target)
                            mir/allocate-registers)) target))))

(defn- instructions-in-block
  "Body of LABEL, stopping at the next label or jump."
  [instructions label-id]
  (->> instructions
       (drop-while #(not (and (= :mir/label (:mir/op %))
                              (= label-id (:mir/id %)))))
       next
       (take-while #(not (contains? #{:mir/label :mir/jump} (:mir/op %))))
       vec))

(def count-down-reload-module
  "Call, then `if`: then-arm returns acc, else-arm adds to acc. A reload of
  acc on the then path must not satisfy the else path."
  {:gmir/version 3
   :gmir/entry 'count-down
   :gmir/functions
   [{:gmir/name 'id :gmir/arity 1
     :gmir/instructions
     [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
      {:gmir/op :gmir/return :gmir/value v0}]}
    {:gmir/name 'count-down :gmir/arity 2
     :gmir/instructions
     [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
      {:gmir/op :gmir/argument :gmir/dst v1 :gmir/index 1}
      {:gmir/op :gmir/call :gmir/dst v2 :gmir/callee 'id
       :gmir/arguments [v0]}
      {:gmir/op :gmir/branch-zero :gmir/test v0 :gmir/target :test.label/else}
      {:gmir/op :gmir/label :gmir/id :test.label/then}
      {:gmir/op :gmir/label :gmir/id :test.label/then-exit}
      {:gmir/op :gmir/jump :gmir/target :test.label/join}
      {:gmir/op :gmir/label :gmir/id :test.label/else}
      {:gmir/op :gmir/constant :gmir/dst v3 :gmir/value 1}
      {:gmir/op :gmir/add :gmir/dst v4 :gmir/left v1 :gmir/right v3}
      {:gmir/op :gmir/label :gmir/id :test.label/else-exit}
      {:gmir/op :gmir/jump :gmir/target :test.label/join}
      {:gmir/op :gmir/label :gmir/id :test.label/join}
      {:gmir/op :gmir/phi :gmir/dst v5
       :gmir/incomings
       [{:gmir/predecessor :test.label/then-exit :gmir/value v1}
        {:gmir/predecessor :test.label/else-exit :gmir/value v4}]}
      {:gmir/op :gmir/return :gmir/value v5}]}]})

(deftest v3-aarch64-preserves-entry-value-and-x86-retains-scratch-plan
  (doseq [target mir/targets]
    (let [allocated (->> count-down-reload-module
                         (mir/select-target target)
                         mir/allocate-registers)
          caller (second (:mir/functions allocated))
          instructions (:mir/instructions caller)
          else (instructions-in-block instructions :test.label/else)
          add (first (filter #(= :mir/add (:mir/op %)) else))]
      (is (= :call-live (:mir/frame-policy caller)) target)
      (is (some? add) target)
      (if (= :aarch64 target)
        (do
          (is (contains? (set (get mir/preserved-registers target)) (:mir/left add))
              "AArch64 keeps the call-crossing entry value in a callee-saved register")
          (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load} (:mir/op %))
                        instructions)
              "AArch64 does not materialize a slot for a preserved entry value"))
        (is (some #(and (= :mir/spill-load (:mir/op %))
                        (= (:mir/dst %) (:mir/left add)))
                  else)
            "x86-64 retains the established scratch-first entry plan"))
      (is (seq (value-ops-unbacked-by-store instructions))
          (str target " must not fall back to all-vreg"))
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)) target))))

(defn- call-branch-wide-module
  "WIDTH calls, all results live until a join. All-vreg would assign a slot
  per SSA value; the linear scanner's slots are bounded by live-across
  values that do not fit in the preserved tier."
  [width]
  (let [arg (gmir/vreg 0)
        results (mapv gmir/vreg (range 1 (inc width)))
        calls (mapv (fn [dst]
                      {:gmir/op :gmir/call :gmir/dst dst :gmir/callee 'add-one
                       :gmir/arguments [arg]})
                    results)
        [sum-insns sum-vreg]
        (reduce (fn [[insns acc] result]
                  (let [dst (gmir/vreg (+ 100 (count insns)))]
                    [(conj insns {:gmir/op :gmir/add :gmir/dst dst
                                  :gmir/left acc :gmir/right result})
                     dst]))
                [[] (first results)]
                (rest results))
        zero (gmir/vreg 200)
        join (gmir/vreg 201)]
    {:gmir/version 3
     :gmir/entry 'main
     :gmir/functions
     [{:gmir/name 'add-one :gmir/arity 1
       :gmir/instructions
       [{:gmir/op :gmir/argument :gmir/dst v0 :gmir/index 0}
        {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 1}
        {:gmir/op :gmir/add :gmir/dst v2 :gmir/left v0 :gmir/right v1}
        {:gmir/op :gmir/return :gmir/value v2}]}
      {:gmir/name 'main :gmir/arity 1
       :gmir/instructions
       (vec (concat
             [{:gmir/op :gmir/argument :gmir/dst arg :gmir/index 0}]
             calls
             [{:gmir/op :gmir/branch-zero :gmir/test arg
               :gmir/target :test.label/else}
              {:gmir/op :gmir/label :gmir/id :test.label/then}]
             sum-insns
             [{:gmir/op :gmir/label :gmir/id :test.label/then-exit}
              {:gmir/op :gmir/jump :gmir/target :test.label/join}
              {:gmir/op :gmir/label :gmir/id :test.label/else}
              {:gmir/op :gmir/constant :gmir/dst zero :gmir/value 0}
              {:gmir/op :gmir/label :gmir/id :test.label/else-exit}
              {:gmir/op :gmir/jump :gmir/target :test.label/join}
              {:gmir/op :gmir/label :gmir/id :test.label/join}
              {:gmir/op :gmir/phi :gmir/dst join
               :gmir/incomings
               [{:gmir/predecessor :test.label/then-exit :gmir/value sum-vreg}
                {:gmir/predecessor :test.label/else-exit :gmir/value zero}]}
              {:gmir/op :gmir/return :gmir/value join}]))}]}))

(deftest v3-eight-live-calls-with-a-join-do-not-take-all-vreg
  (let [width 8
        module (call-branch-wide-module width)]
    (doseq [target mir/targets]
      (let [caller (second (:mir/functions
                            (->> module (mir/select-target target)
                                 mir/allocate-registers)))
            instructions (:mir/instructions caller)
            preserved (count (get mir/preserved-registers target))]
        (is (= :call-live (:mir/frame-policy caller)) target)
        (is (<= (:mir/frame-slots caller) (inc (- width preserved)))
            (str target " spills at most the live-across excess, not every value"))
        (is (< (count (filter #(= :mir/spill-store (:mir/op %)) instructions))
               (* 3 width))
            (str target " is not storing every SSA value"))
        (is (seq (value-ops-unbacked-by-store instructions)) target)
        (is (not-any? gmir/vreg? (tree-seq coll? seq caller)) target)))))

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

(deftest v3-aarch64-live-entry-arguments-start-in-preserved-registers
  ;; This is the scalar shape produced for loop/recur with a real call in the
  ;; body.  `i` and `acc` enter in ABI registers but survive `id`; assigning
  ;; them scratch-first would store and reload both values on every iteration.
  (let [i (gmir/vreg 0)
        acc (gmir/vreg 1)
        zero (gmir/vreg 2)
        done? (gmir/vreg 3)
        call-one (gmir/vreg 4)
        stepped (gmir/vreg 5)
        sub-one (gmir/vreg 6)
        next-i (gmir/vreg 7)
        next-acc (gmir/vreg 8)
        module {:gmir/version 3
                :gmir/entry 'loop-helper
                :gmir/functions
                [{:gmir/name 'id :gmir/arity 1
                  :gmir/instructions
                  [{:gmir/op :gmir/argument :gmir/dst (gmir/vreg 10)
                    :gmir/index 0}
                   {:gmir/op :gmir/return :gmir/value (gmir/vreg 10)}]}
                 {:gmir/name 'loop-helper :gmir/arity 2
                  :gmir/instructions
                  [{:gmir/op :gmir/argument :gmir/dst i :gmir/index 0}
                   {:gmir/op :gmir/argument :gmir/dst acc :gmir/index 1}
                   {:gmir/op :gmir/constant :gmir/dst zero :gmir/value 0}
                   {:gmir/op :gmir/equal :gmir/dst done?
                    :gmir/left i :gmir/right zero}
                   {:gmir/op :gmir/branch-zero :gmir/test done?
                    :gmir/target :test.label/continue}
                   {:gmir/op :gmir/return :gmir/value acc}
                   {:gmir/op :gmir/label :gmir/id :test.label/continue}
                   {:gmir/op :gmir/constant :gmir/dst call-one :gmir/value 1}
                   {:gmir/op :gmir/call :gmir/dst stepped
                    :gmir/callee 'id :gmir/arguments [call-one]}
                   {:gmir/op :gmir/constant :gmir/dst sub-one :gmir/value 1}
                   {:gmir/op :gmir/subtract :gmir/dst next-i
                    :gmir/left i :gmir/right sub-one}
                   {:gmir/op :gmir/add :gmir/dst next-acc
                    :gmir/left acc :gmir/right stepped}
                   {:gmir/op :gmir/tail-call :gmir/callee 'loop-helper
                    :gmir/arguments [next-i next-acc]}]}]}]
    (doseq [target mir/targets]
      (let [function (second (:mir/functions
                              (->> module (mir/select-target target)
                                   mir/allocate-registers)))
            instructions (:mir/instructions function)
            preserved (set (get mir/preserved-registers target))]
        (is (= :call-live (:mir/frame-policy function)) target)
        (is (= (if (= :aarch64 target) 0 2) (:mir/frame-slots function)) target)
        (is (= (if (= :aarch64 target) 0 2)
               (count (filter #(= :mir/spill-store (:mir/op %)) instructions))) target)
        (is (= (if (= :aarch64 target) 0 2)
               (count (filter #(= :mir/spill-load (:mir/op %)) instructions))) target)
        (is (= (if (= :aarch64 target) 2 1)
               (count (mir/saved-registers target instructions))) target)
        (is (every? preserved (mir/saved-registers target instructions)) target)
        (is (= :mir/tail-call (:mir/op (peek instructions))) target)))))

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
    ;; it spills two values; with the tiers on offer it takes none.
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

(deftest call-capable-expiration-preserves-register-tier-classification
  ;; A callee-saved register released by a crossing value must remain reserve.
  ;; Putting it on the scratch list makes a later short-lived value incur an
  ;; otherwise avoidable prologue/epilogue save pair.
  (let [expire-in-pool @#'kotoba.mir/expire-assigned-in-pool]
    (doseq [target mir/targets]
      (let [scratch (first (get mir/physical-registers target))
            preserved (first (get mir/preserved-registers target))
            assigned {v0 scratch v1 preserved}
            state {:assigned assigned
                   :free (vec (remove #{scratch preserved}
                                      (get mir/physical-registers target)))
                   :reserve (vec (remove #{preserved}
                                         (get mir/preserved-registers target)))}
            after-preserved (expire-in-pool target state [v1])
            after-both (expire-in-pool target after-preserved [v0])]
        (is (not (some #{preserved} (:free after-preserved))) target)
        (is (some #{preserved} (:reserve after-preserved)) target)
        (is (some #{scratch} (:free after-both)) target)
        (is (not (some #{scratch} (:reserve after-both))) target)))))

(deftest sequential-call-crossings-reuse-one-preserved-register
  ;; The first value crossing a call dies before the second crossing value is
  ;; defined. Its callee-saved register must return to reserve; otherwise the
  ;; second value consumes another callee-saved register and adds an avoidable
  ;; prologue/epilogue save pair. The label selects the CFG-capable allocator.
  (let [[a call-one result-one b call-two result-two]
        (mapv gmir/vreg (range 6))
        module {:gmir/version 3
                :gmir/entry 'main
                :gmir/functions
                [{:gmir/name 'identity :gmir/arity 0
                  :gmir/instructions
                  [{:gmir/op :gmir/constant :gmir/dst (gmir/vreg 20)
                    :gmir/value 1}
                   {:gmir/op :gmir/return :gmir/value (gmir/vreg 20)}]}
                 {:gmir/name 'main :gmir/arity 0
                  :gmir/instructions
                  [{:gmir/op :gmir/label :gmir/id :test.label/entry}
                   {:gmir/op :gmir/constant :gmir/dst a :gmir/value 40}
                   {:gmir/op :gmir/call :gmir/dst call-one
                    :gmir/callee 'identity :gmir/arguments []}
                   {:gmir/op :gmir/add :gmir/dst result-one
                    :gmir/left a :gmir/right call-one}
                   {:gmir/op :gmir/constant :gmir/dst b :gmir/value 50}
                   {:gmir/op :gmir/call :gmir/dst call-two
                    :gmir/callee 'identity :gmir/arguments []}
                   {:gmir/op :gmir/add :gmir/dst result-two
                    :gmir/left b :gmir/right call-two}
                   {:gmir/op :gmir/return :gmir/value result-two}]}]}]
    (doseq [target mir/targets]
      (let [function (->> module
                          (mir/select-target target)
                          mir/allocate-registers
                          :mir/functions
                          second)
            instructions (:mir/instructions function)]
        (is (= :call-live (:mir/frame-policy function)) target)
        (is (= 1 (count (mir/saved-registers target instructions))) target)
        (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load}
                                  (:mir/op %))
                      instructions) target)))))

(defn- simultaneous-live-sum
  "N independent constants, all live, then a left-fold so the last definition
  is the peak. One past the pool must spill; the pool itself must not."
  [n]
  (let [values (mapv gmir/vreg (range n))]
    {:gmir/version 1
     :gmir/instructions
     (vec (concat
           (map-indexed (fn [index value]
                          {:gmir/op :gmir/constant :gmir/dst value
                           :gmir/value index})
                        values)
           (second
            (reduce (fn [[acc ops] value]
                      (let [dst (gmir/vreg (+ n (count ops)))]
                        [dst (conj ops {:gmir/op :gmir/add :gmir/dst dst
                                        :gmir/left acc :gmir/right value})]))
                    [(first values) []]
                    (rest values)))
           [{:gmir/op :gmir/return
             :gmir/value (gmir/vreg (+ n (dec n) -1))}]))}))

(deftest a-body-that-fits-the-pool-still-does-not-touch-the-stack
  (doseq [target mir/targets]
    (let [pool (count (mir/allocator-pool target {:leaf? true}))
          allocated (->> (simultaneous-live-sum pool)
                         (mir/select-target target)
                         mir/allocate-registers)]
      (is (zero? (:mir/frame-slots allocated)) target)
      (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load} (:mir/op %))
                    (:mir/instructions allocated))
          target))))

(deftest one-past-the-pool-spills-one-value-not-every-value
  (doseq [target mir/targets]
    (let [pool (count (mir/allocator-pool target {:leaf? true}))
          n (inc pool)
          allocated (->> (simultaneous-live-sum n)
                         (mir/select-target target)
                         mir/allocate-registers)
          slots (:mir/frame-slots allocated)
          stores (filterv #(= :mir/spill-store (:mir/op %))
                          (:mir/instructions allocated))]
      (is (pos? slots) target)
      (is (< slots n) target)
      (is (= 1 slots)
          (str target " spills the one value that does not fit, not " n))
      (is (= 1 (count (distinct (map :mir/slot stores)))) target)
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)) target)
      (is (= allocated
             (->> (simultaneous-live-sum n)
                  (mir/select-target target)
                  mir/allocate-registers))
          target))))

;; ── proportional spilling ────────────────────────────────────────────────────

(def all-vreg-slot-reuse-program
  {:gmir/version 1
   :gmir/instructions
   [{:gmir/op :gmir/constant :gmir/dst v0 :gmir/value 1}
    {:gmir/op :gmir/constant :gmir/dst v1 :gmir/value 2}
    {:gmir/op :gmir/add :gmir/dst v2 :gmir/left v0 :gmir/right v1}
    {:gmir/op :gmir/constant :gmir/dst v3 :gmir/value 3}
    {:gmir/op :gmir/add :gmir/dst v4 :gmir/left v2 :gmir/right v3}
    {:gmir/op :gmir/return :gmir/value v4}]})

(deftest conservative-all-vreg-reuses-dead-frame-slots
  (doseq [target mir/targets]
    (let [selected (mir/select-target target all-vreg-slot-reuse-program)
          allocate-with-spills @#'kotoba.mir/allocate-with-spills
          allocated (allocate-with-spills selected {})
          stores (filterv #(= :mir/spill-store (:mir/op %))
                          (:mir/instructions allocated))]
      (is (= 2 (:mir/frame-slots allocated))
          (str target " colors five SSA values into the two simultaneously-live slots"))
      (is (= [0 1 0 1 0] (mapv :mir/slot stores)) target)
      (is (= allocated (allocate-with-spills selected {})) target)
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)) target))))

(deftest a-spill-store-sits-at-the-definition-not-where-the-register-ran-out
  ;; Four values are live across a branch, and the arms need registers the
  ;; scratch tier does not have. The point where a register runs out is inside
  ;; one arm; the reload is in the other. A store emitted where the eviction
  ;; happens would write a slot on a path that was not taken, and the other arm
  ;; would read whatever was there. A definition dominates every use of its
  ;; value, so that is where the store belongs.
  (with-scratch-tier-only
    (let [[a b c d x1 x2 x3 then-y else-y join result] (map gmir/vreg (range 11))
          program
          {:gmir/version 2
           :gmir/instructions
           [{:gmir/op :gmir/constant :gmir/dst a :gmir/value 1}
            {:gmir/op :gmir/constant :gmir/dst b :gmir/value 2}
            {:gmir/op :gmir/constant :gmir/dst c :gmir/value 3}
            {:gmir/op :gmir/constant :gmir/dst d :gmir/value 4}
            ;; `a` dies here, leaving b, c and d live in a four-register tier.
            {:gmir/op :gmir/branch-zero :gmir/test a :gmir/target :test.label/else}
            {:gmir/op :gmir/label :gmir/id :test.label/then}
            {:gmir/op :gmir/add :gmir/dst x1 :gmir/left c :gmir/right d}
            ;; The fourth register is gone and neither operand of this dies, so
            ;; something is evicted -- here, inside this arm. The victim is the
            ;; value wanted furthest away, which is `b`, because its next use is
            ;; in the arm that this one does not reach.
            {:gmir/op :gmir/add :gmir/dst x2 :gmir/left c :gmir/right d}
            {:gmir/op :gmir/add :gmir/dst x3 :gmir/left x1 :gmir/right x2}
            {:gmir/op :gmir/add :gmir/dst then-y :gmir/left x3 :gmir/right d}
            {:gmir/op :gmir/label :gmir/id :test.label/then-exit}
            {:gmir/op :gmir/jump :gmir/target :test.label/join}
            {:gmir/op :gmir/label :gmir/id :test.label/else}
            ;; ...and this arm reads it.
            {:gmir/op :gmir/add :gmir/dst else-y :gmir/left b :gmir/right c}
            {:gmir/op :gmir/label :gmir/id :test.label/else-exit}
            {:gmir/op :gmir/jump :gmir/target :test.label/join}
            {:gmir/op :gmir/label :gmir/id :test.label/join}
            {:gmir/op :gmir/phi :gmir/dst join
             :gmir/incomings [{:gmir/predecessor :test.label/then-exit :gmir/value then-y}
                              {:gmir/predecessor :test.label/else-exit :gmir/value else-y}]}
            {:gmir/op :gmir/add :gmir/dst result :gmir/left join :gmir/right d}
            {:gmir/op :gmir/return :gmir/value result}]}
          instructions (:mir/instructions
                        (->> program (mir/select-target :x86-64)
                             mir/allocate-registers))
          numbered (vec (map-indexed vector instructions))
          stores (filter (fn [[_ i]] (= :mir/spill-store (:mir/op i))) numbered)
          loads (filter (fn [[_ i]] (= :mir/spill-load (:mir/op i))) numbered)
          label-at (fn [position]
                     (->> (subvec instructions 0 position)
                          (filter #(= :mir/label (:mir/op %)))
                          last :mir/id))]
      (is (seq stores) "the program has to spill for the rest to mean anything")
      (is (seq loads))
      (doseq [[position store] stores]
        (is (pos? position))
        (is (= (:mir/src store) (:mir/dst (nth instructions (dec position))))
            (str "the store at " position " must follow the instruction that "
                 "defines the register it stores")))
      ;; The property the placement exists for: nothing reloads a slot from a
      ;; block other than the one that wrote it, unless the writer's block
      ;; dominates -- and here the only dominating block is the entry.
      (doseq [[position load] loads]
        (let [slot (:mir/slot load)
              writer (first (filter (fn [[_ store]] (= slot (:mir/slot store)))
                                    stores))]
          (is writer (str "slot " slot " is loaded at " position " and never stored"))
          (when writer
            (is (< (first writer) position) "stored before it is loaded")
            (is (nil? (label-at (first writer)))
                (str "slot " slot " is stored inside " (label-at (first writer))
                     " and loaded inside " (label-at position)))))))))

(defn- has-back-edge?
  "True when a jump or branch targets a label at or before it. Same scan as
  kotoba.mir/back-edge?, kept here because that predicate is private."
  [instructions]
  (let [label-index (into {}
                          (keep-indexed
                           (fn [index instruction]
                             (when (= :mir/label (:mir/op instruction))
                               [(:mir/id instruction) index]))
                           instructions))]
    (boolean
     (some (fn [[index instruction]]
             (and (contains? #{:mir/jump :mir/branch-zero} (:mir/op instruction))
                  (when-let [target (get label-index (:mir/target instruction))]
                    (<= target index))))
           (map-indexed vector instructions)))))

(def call-and-back-edge-module
  "A function that contains a direct call and a backward jump, with `acc` and
  `n` live across both. Arguments are a prefix so `entry-argument-plan` can
  start. Kotoba `loop/recur` desugars to a recursive helper
  (frontend-destructuring-loop-test), and string-search loops live in the
  runtime, so this shape is not in the source corpus that iteration 21 ran."
  (let [n0 (gmir/vreg 0)
        acc0 (gmir/vreg 1)
        n (gmir/vreg 2)
        acc (gmir/vreg 3)
        one (gmir/vreg 4)
        stepped (gmir/vreg 5)
        acc1 (gmir/vreg 6)
        n1 (gmir/vreg 7)]
    {:gmir/version 3
     :gmir/entry 'count-loop
     :gmir/functions
     [{:gmir/name 'id :gmir/arity 1
       :gmir/instructions
       [{:gmir/op :gmir/argument :gmir/dst (gmir/vreg 0) :gmir/index 0}
        {:gmir/op :gmir/return :gmir/value (gmir/vreg 0)}]}
      {:gmir/name 'count-loop :gmir/arity 1
       :gmir/instructions
       [{:gmir/op :gmir/argument :gmir/dst n0 :gmir/index 0}
        {:gmir/op :gmir/constant :gmir/dst acc0 :gmir/value 0}
        {:gmir/op :gmir/label :gmir/id :test.label/preheader}
        {:gmir/op :gmir/jump :gmir/target :test.label/header}
        {:gmir/op :gmir/label :gmir/id :test.label/header}
        {:gmir/op :gmir/phi :gmir/dst n
         :gmir/incomings [{:gmir/predecessor :test.label/preheader :gmir/value n0}
                          {:gmir/predecessor :test.label/latch :gmir/value n1}]}
        {:gmir/op :gmir/phi :gmir/dst acc
         :gmir/incomings [{:gmir/predecessor :test.label/preheader :gmir/value acc0}
                          {:gmir/predecessor :test.label/latch :gmir/value acc1}]}
        {:gmir/op :gmir/branch-zero :gmir/test n :gmir/target :test.label/done}
        {:gmir/op :gmir/label :gmir/id :test.label/body}
        {:gmir/op :gmir/constant :gmir/dst one :gmir/value 1}
        {:gmir/op :gmir/call :gmir/dst stepped :gmir/callee 'id
         :gmir/arguments [one]}
        {:gmir/op :gmir/add :gmir/dst acc1 :gmir/left acc :gmir/right stepped}
        {:gmir/op :gmir/subtract :gmir/dst n1 :gmir/left n :gmir/right one}
        {:gmir/op :gmir/label :gmir/id :test.label/latch}
        {:gmir/op :gmir/jump :gmir/target :test.label/header}
        {:gmir/op :gmir/label :gmir/id :test.label/done}
        {:gmir/op :gmir/return :gmir/value acc}]}]}))

(deftest v3-call-plus-back-edge-is-routed-to-call-live
  (doseq [target mir/targets]
    (let [allocated (->> call-and-back-edge-module
                         (mir/select-target target)
                         mir/allocate-registers)
          looper (->> allocated :mir/functions
                      (filter #(= 'count-loop (:mir/name %)))
                      first)
          instructions (:mir/instructions looper)]
      (is (has-back-edge? instructions) target)
      (is (= :call-live (:mir/frame-policy looper)) target)
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)) target))))

(deftest conservative-all-vreg-colors-a-call-loop-with-cfg-liveness
  (doseq [target mir/targets]
    (let [selected (mir/select-target target call-and-back-edge-module)
          function (second (:mir/functions selected))
          virtual {:mir/version 3 :mir/target target :mir/registers :virtual
                   :mir/instructions (:mir/instructions function)}
          lower-phis @#'kotoba.mir/lower-phis
          allocate-with-spills @#'kotoba.mir/allocate-with-spills
          {:keys [program merge-dst-by-slot]} (lower-phis virtual)
          allocated (allocate-with-spills program merge-dst-by-slot)]
      (is (= 4 (:mir/frame-slots allocated))
          (str target " colors eight loop SSA values into four live slots"))
      (is (= allocated (allocate-with-spills program merge-dst-by-slot)) target)
      (is (has-back-edge? (:mir/instructions allocated)) target)
      (is (not-any? gmir/vreg? (tree-seq coll? seq allocated)) target))))

(def countdown-module
  "A second terminating call+loop: only `n` is carried, body calls `id(n)`.
  Arguments are a prefix so `entry-argument-plan` can start. After
  `lower-phis`, latch values are stored after their defs."
  (let [n0 (gmir/vreg 0)
        n (gmir/vreg 1)
        n1 (gmir/vreg 2)
        one (gmir/vreg 3)
        ignored (gmir/vreg 4)]
    {:gmir/version 3
     :gmir/entry 'countdown
     :gmir/functions
     [{:gmir/name 'id :gmir/arity 1
       :gmir/instructions
       [{:gmir/op :gmir/argument :gmir/dst (gmir/vreg 0) :gmir/index 0}
        {:gmir/op :gmir/return :gmir/value (gmir/vreg 0)}]}
      {:gmir/name 'countdown :gmir/arity 1
       :gmir/instructions
       [{:gmir/op :gmir/argument :gmir/dst n0 :gmir/index 0}
        {:gmir/op :gmir/label :gmir/id :test.label/preheader}
        {:gmir/op :gmir/jump :gmir/target :test.label/header}
        {:gmir/op :gmir/label :gmir/id :test.label/header}
        {:gmir/op :gmir/phi :gmir/dst n
         :gmir/incomings [{:gmir/predecessor :test.label/preheader :gmir/value n0}
                          {:gmir/predecessor :test.label/latch :gmir/value n1}]}
        {:gmir/op :gmir/branch-zero :gmir/test n :gmir/target :test.label/done}
        {:gmir/op :gmir/label :gmir/id :test.label/body}
        {:gmir/op :gmir/call :gmir/dst ignored :gmir/callee 'id
         :gmir/arguments [n]}
        {:gmir/op :gmir/constant :gmir/dst one :gmir/value 1}
        {:gmir/op :gmir/subtract :gmir/dst n1 :gmir/left n :gmir/right one}
        {:gmir/op :gmir/label :gmir/id :test.label/latch}
        {:gmir/op :gmir/jump :gmir/target :test.label/header}
        {:gmir/op :gmir/label :gmir/id :test.label/done}
        {:gmir/op :gmir/return :gmir/value n}]}]}))

(defn- looper-policy [module fname target]
  (let [allocated (->> module
                       (mir/select-target target)
                       mir/allocate-registers)
        looper (->> allocated :mir/functions
                    (filter #(= fname (:mir/name %)))
                    first)]
    (:mir/frame-policy looper)))

(deftest v3-prefix-argument-call-loops-complete-the-scanner
  ;; Iteration 23 read :all-vregs-with-override as last-uses failing on a
  ;; header phi. The throw was :non-prefix-argument: both fixtures started
  ;; with a label, and entry-argument-plan tags that :spill-required. After
  ;; lower-phis, latch last-uses are after their defs. Arguments first, the
  ;; scanner completes. Production uses that path; leftover pressure still
  ;; falls back to all-vreg via :spill-required.
  (doseq [target mir/targets
          [module fname] [[call-and-back-edge-module 'count-loop]
                          [countdown-module 'countdown]]]
    (is (= :call-live (looper-policy module fname target))
        [target fname])))

(deftest cfg-liveness-extends-last-use-past-textual-use-on-back-edge
  (let [cfg-last-uses @#'kotoba.mir/cfg-last-uses
        [x y] (map gmir/vreg [0 1])
        instructions
        [{:mir/op :mir/label :mir/id :loop}
         {:mir/op :mir/add :mir/dst y :mir/left x :mir/right x}
         {:mir/op :mir/jump :mir/target :loop}]
        last-use (cfg-last-uses instructions)]
    (is (= 2 (get last-use x))
        "x is textually last used at the add, but stays live through the back edge")))

(deftest cfg-dominator-tree-linear-fallthrough
  (let [cfg-dominator-analysis @#'kotoba.mir/cfg-dominator-analysis
        cfg-dominates? @#'kotoba.mir/cfg-dominates?
        [x] (map gmir/vreg [0])
        instructions [{:mir/op :mir/add :mir/dst x :mir/left x :mir/right x}
                      {:mir/op :mir/jump :mir/target :done}
                      {:mir/op :mir/label :mir/id :done}
                      {:mir/op :mir/return :mir/src x}]
        {:keys [dominators immediate-dominators]} (cfg-dominator-analysis instructions)]
    (is (= 2 (count dominators)))
    (is (= #{0} (nth dominators 0)))
    (is (= #{0 1} (nth dominators 1)))
    (is (= 0 (nth immediate-dominators 1)))
    (is (cfg-dominates? dominators 0 1))
    (is (not (cfg-dominates? dominators 1 0)))))

(deftest cfg-dominator-tree-if-else-merge
  (let [cfg-dominator-analysis @#'kotoba.mir/cfg-dominator-analysis
        [cond x y] (map gmir/vreg [0 1 2])
        instructions [{:mir/op :mir/branch-zero :mir/left cond :mir/target :else}
                      {:mir/op :mir/label :mir/id :then}
                      {:mir/op :mir/add :mir/dst x :mir/left x :mir/right x}
                      {:mir/op :mir/jump :mir/target :merge}
                      {:mir/op :mir/label :mir/id :else}
                      {:mir/op :mir/add :mir/dst y :mir/left y :mir/right y}
                      {:mir/op :mir/jump :mir/target :merge}
                      {:mir/op :mir/label :mir/id :merge}
                      {:mir/op :mir/return :mir/src x}]
        {:keys [dominators immediate-dominators]} (cfg-dominator-analysis instructions)]
    (is (= #{0 1} (nth dominators 1)))
    (is (= #{0 2} (nth dominators 2)))
    (is (= #{0 3} (nth dominators 3)))
    (is (= 0 (nth immediate-dominators 1)))
    (is (= 0 (nth immediate-dominators 2)))
    (is (= 0 (nth immediate-dominators 3)))))

(deftest cfg-dominator-tree-loop-header
  (let [cfg-dominator-analysis @#'kotoba.mir/cfg-dominator-analysis
        [x] (map gmir/vreg [0])
        instructions [{:mir/op :mir/branch-zero :mir/left x :mir/target :exit}
                      {:mir/op :mir/label :mir/id :loop}
                      {:mir/op :mir/add :mir/dst x :mir/left x :mir/right x}
                      {:mir/op :mir/jump :mir/target :loop}
                      {:mir/op :mir/label :mir/id :exit}
                      {:mir/op :mir/return :mir/src x}]
        {:keys [dominators immediate-dominators]} (cfg-dominator-analysis instructions)]
    (is (= 3 (count dominators)))
    (is (= #{0 1} (nth dominators 1)))
    (is (= #{0 2} (nth dominators 2)))
    (is (= 0 (nth immediate-dominators 1)))
    (is (= 0 (nth immediate-dominators 2)))))

(deftest cfg-liveness-does-not-carry-loop-local-temporaries-over-the-back-edge
  ;; Each constant and sum is defined and consumed inside the loop block. A
  ;; use-set that includes reads after a local definition falsely carries all
  ;; thirty values through the self edge. Before the fix that pressure created
  ;; 12 x86-64 frame slots and 3 AArch64 slots.
  (let [values (mapv gmir/vreg (range 30))
        triples (partition 3 values)
        body (mapcat (fn [index [left right sum]]
                       [{:gmir/op :gmir/constant :gmir/dst left
                         :gmir/value index}
                        {:gmir/op :gmir/constant :gmir/dst right
                         :gmir/value (inc index)}
                        {:gmir/op :gmir/add :gmir/dst sum
                         :gmir/left left :gmir/right right}])
                     (range)
                     triples)
        program {:gmir/version 2
                 :gmir/instructions
                 (vec (concat [{:gmir/op :gmir/label
                                :gmir/id :test.label/header}]
                              body
                              [{:gmir/op :gmir/jump
                                :gmir/target :test.label/header}]))}]
    (doseq [target mir/targets]
      (let [allocated (->> program
                           (mir/select-target target)
                           mir/allocate-registers)]
        (is (zero? (:mir/frame-slots allocated)) target)
        (is (not-any? #(contains? #{:mir/spill-store :mir/spill-load}
                                  (:mir/op %))
                      (:mir/instructions allocated)) target)
        (is (= allocated
               (->> program (mir/select-target target) mir/allocate-registers))
            target)))))
