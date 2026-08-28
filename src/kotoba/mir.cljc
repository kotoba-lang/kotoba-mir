(ns kotoba.mir
  "Closed target-selected Machine IR and deterministic allocation."
  (:require [clojure.set :as set]
            [kotoba.gmir :as gmir]))

(def version 3)
(def supported-versions #{1 2 3})
(def targets #{:x86-64 :aarch64})

(def physical-registers
  "The always-available scratch tier. Every allocation path may use these, and
  the conservative all-vreg path uses only these."
  {:x86-64 [:x86-64/rax :x86-64/rcx :x86-64/rdx :x86-64/r8]
   :aarch64 [:aarch64/x0 :aarch64/x1 :aarch64/x2 :aarch64/x3]})

(def leaf-registers
  "Caller-saved registers a function that calls nothing may use without saving
  anything. On x86-64 these are the incoming argument registers, dead once the
  entry plan has copied the arguments out; on AArch64 they are the temporaries
  below the encoder's own scratch pair. A function that makes a call must not
  use them, so only the no-call paths are offered this tier."
  {:x86-64 [:x86-64/rdi :x86-64/rsi]
   :aarch64 [:aarch64/x5 :aarch64/x6 :aarch64/x8 :aarch64/x9
             :aarch64/x10 :aarch64/x11 :aarch64/x12]})

(def preserved-registers
  "Callee-saved registers. Available on every path, at the cost of a save and a
  restore in the frame for exactly the ones a function actually assigns --
  which is why allocation reports them rather than the frame guessing."
  {:x86-64 [:x86-64/rbx :x86-64/r12 :x86-64/r13 :x86-64/r14 :x86-64/r15]
   :aarch64 [:aarch64/x19 :aarch64/x20 :aarch64/x21 :aarch64/x22
             :aarch64/x23 :aarch64/x24 :aarch64/x25 :aarch64/x26]})

(defn allocator-pool
  "The registers an allocation path may hand out. The scratch tier comes first
  so that a function small enough to stay inside it costs no frame save; the
  preserved tier comes last for the same reason."
  [target {:keys [leaf?]}]
  (vec (concat (get physical-registers target)
               (when leaf? (get leaf-registers target))
               (get preserved-registers target))))

(defn saved-registers
  "Which preserved registers a physical instruction sequence names, in pool
  order, so a frame can save them in order and restore them in reverse.

  Derived rather than carried: a field saying which registers a body uses has
  to be kept equal to the body, and the two drift silently in the direction
  that omits a save. Encoders call this on the stream they are about to emit."
  [target instructions]
  (let [preserved (set (get preserved-registers target))]
    (into []
          (filter (into #{} (mapcat (fn [instruction]
                                      (filter preserved
                                              (tree-seq coll? seq instruction)))
                                    instructions)))
          (get preserved-registers target))))

(def call-argument-registers
  {:x86-64 [:x86-64/rdi :x86-64/rsi :x86-64/rdx :x86-64/rcx :x86-64/r8]
   :aarch64 [:aarch64/x0 :aarch64/x1 :aarch64/x2 :aarch64/x3 :aarch64/x4]})

(def runtime-argument-registers
  {:x86-64 [:x86-64/rsi :x86-64/rdx :x86-64/rcx]
   :aarch64 [:aarch64/x1 :aarch64/x2 :aarch64/x3]})

(def runtime-context-offsets
  {:pair 56 :pair-first 64 :pair-second 72
   :kgraph-assert! 80 :kgraph-get 88 :kgraph-count 96
   :kgraph-entity-at 104
   :string-byte-length 72 :string=? 112 :string-concat 120
   :string-substring 136 :string-code-point-at 144
   :vector-new-empty 152 :vector-conj 160 :vector-count 168
   :vector-at 176 :vector-assoc 184 :vector-drop 192})

(def capability-argument-registers
  {:x86-64 {:i64 [:x86-64/rdx]
            :string [:x86-64/r8]
            :option-i64 [:x86-64/r8]
            :result-i64 [:x86-64/r8]
            :clock-v1 [:x86-64/r8]
            :dataspace-v1 [:x86-64/r8]
            :ui-commit-v1 [:x86-64/r8]
            :ui-event-v1 [:x86-64/r8]}
   :aarch64 {:i64 [:aarch64/x2]
            :string [:aarch64/x4]
            :option-i64 [:aarch64/x4]
            :result-i64 [:aarch64/x4]
            :clock-v1 [:aarch64/x4]
            :dataspace-v1 [:aarch64/x4]
            :ui-commit-v1 [:aarch64/x4]
            :ui-event-v1 [:aarch64/x4]}})

(def capability-context-offsets
  {:i64 48 :string 128 :option-i64 128 :result-i64 128 :clock-v1 128
   :dataspace-v1 128 :ui-commit-v1 128 :ui-event-v1 128})

(def return-registers
  {:x86-64 :x86-64/rax
   :aarch64 :aarch64/x0})

(defn- reject! [problem instruction]
  (throw (ex-info (str "MIR rejected: " (name problem))
                  {:phase :mir :problem problem :instruction instruction})))

(def instruction-keysets
  {:mir/argument #{:mir/op :mir/dst :mir/index}
   :mir/constant #{:mir/op :mir/dst :mir/value}
   :mir/data-address #{:mir/op :mir/dst :mir/content}
   :mir/add #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/subtract #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/multiply #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/multiply-add #{:mir/op :mir/dst :mir/left :mir/right :mir/addend}
   :mir/multiply-subtract #{:mir/op :mir/dst :mir/left :mir/right :mir/addend}
   :mir/quotient #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/quotient-constant #{:mir/op :mir/dst :mir/left :mir/divisor}
   :mir/bit-and #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/bit-or #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/bit-xor #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/shift-left #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/shift-right-signed #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/shift-right-unsigned #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-add #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-subtract #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-multiply #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-divide #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-min #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-max #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-sqrt #{:mir/op :mir/dst :mir/input}
   :mir/f64-equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-less-than #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-less-or-equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-greater-than #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-greater-or-equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/f64-unordered #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/kernel-load-u8 #{:mir/op :mir/dst :mir/base :mir/length
                         :mir/index :mir/maximum}
   :mir/kernel-store-u8 #{:mir/op :mir/dst :mir/base :mir/length
                          :mir/index :mir/stored :mir/maximum}
   :mir/kernel-load-u32 #{:mir/op :mir/dst :mir/base :mir/length
                          :mir/index :mir/maximum}
   :mir/kernel-store-u32 #{:mir/op :mir/dst :mir/base :mir/length
                           :mir/index :mir/stored :mir/maximum}
   ;; The lock pair carries the load's fields: three sources in, one value
   ;; out. No `:mir/stored` -- the stored word is fixed by the operation, not
   ;; supplied by the guest.
   :mir/kernel-try-lock-u32 #{:mir/op :mir/dst :mir/base :mir/length
                              :mir/index :mir/maximum}
   :mir/kernel-unlock-u32 #{:mir/op :mir/dst :mir/base :mir/length
                            :mir/index :mir/maximum}
   :mir/kernel-subregion #{:mir/op :mir/dst :mir/base :mir/length
                           :mir/offset :mir/size}
   :mir/equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/less-than #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/greater-than #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/less-or-equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/greater-or-equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/spill-load #{:mir/op :mir/dst :mir/slot}
   :mir/spill-store #{:mir/op :mir/src :mir/slot}
   :mir/move #{:mir/op :mir/dst :mir/src}
   ;; Physical-only AArch64 self-tail re-entry. The boundary carries the
   ;; allocator-owned parameter homes; recur edges have already performed the
   ;; simultaneous assignment into exactly those registers.
   :mir/reentry #{:mir/op :mir/parameters}
   :mir/recur #{:mir/op :mir/arguments}
   :mir/label #{:mir/op :mir/id}
   :mir/branch-zero #{:mir/op :mir/test :mir/target}
   :mir/branch-nonzero #{:mir/op :mir/test :mir/target}
   :mir/jump #{:mir/op :mir/target}
   :mir/phi #{:mir/op :mir/dst :mir/incomings}
   :mir/call #{:mir/op :mir/dst :mir/callee :mir/arguments}
   :mir/tail-call #{:mir/op :mir/callee :mir/arguments}
   :mir/runtime-call #{:mir/op :mir/dst :mir/runtime :mir/context-offset
                       :mir/arguments}
   :mir/x86-privileged #{:mir/op :mir/dst :mir/action :mir/arguments}
   :mir/capability-call #{:mir/op :mir/dst :mir/capability :mir/kind
                          :mir/context-offset :mir/arguments}
   :mir/return #{:mir/op :mir/value}})

(def ^:private v1-operations
  (disj (set (keys instruction-keysets)) :mir/phi :mir/call :mir/tail-call
        :mir/quotient-constant :mir/branch-nonzero :mir/reentry :mir/recur))

(def ^:private v2-operations
  (disj (set (keys instruction-keysets)) :mir/call :mir/tail-call
        :mir/quotient-constant :mir/branch-nonzero :mir/reentry :mir/recur))

(def ^:private v3-operations
  (set (keys instruction-keysets)))

(defn- operations-for [program-version]
  (case program-version
    1 v1-operations
    2 v2-operations
    3 v3-operations
    #{}))

(defn- physical-register? [target value]
  ;; Physical registers are namespaced keywords. Guard that closed type before
  ;; asking a hash set about VALUE: nbb cannot hash a JavaScript BigInt
  ;; primitive (it attempts to attach a closure uid), and integer immediates
  ;; legitimately flow through instruction-sources beside registers.
  (and (keyword? value)
       (contains? (set (concat (get physical-registers target)
                               (get leaf-registers target)
                               (get preserved-registers target)
                               (get call-argument-registers target)))
                  value)))

(defn- call-operation? [op]
  (contains? #{:mir/call :mir/tail-call :mir/runtime-call
               :mir/capability-call} op))

(defn- argument-registers-for-call [target {:mir/keys [op kind]}]
  (case op
    :mir/runtime-call (get runtime-argument-registers target)
    :mir/capability-call (get-in capability-argument-registers [target kind])
    (get call-argument-registers target)))

(defn- validate-flat!
  [{:mir/keys [version target registers instructions frame-slots] :as program}]
  (when-not (and (map? program)
                 (contains? #{#{:mir/version :mir/target :mir/registers :mir/instructions}
                              #{:mir/version :mir/target :mir/registers :mir/instructions
                                :mir/frame-slots}}
                            (set (keys program)))
                 (contains? supported-versions version)
                 (contains? targets target)
                 (contains? #{:virtual :physical} registers)
                 (vector? instructions)
                 (or (nil? frame-slots)
                     (and (= :physical registers)
                          (integer? frame-slots)
                          (<= 0 frame-slots 4095))))
    (reject! :non-canonical-program program))
  (let [register? (if (= :virtual registers)
                    gmir/vreg?
                    #(physical-register? target %))]
    (doseq [instruction instructions]
      (let [op (:mir/op instruction)
            allowed (operations-for version)]
        (when-not (and (contains? allowed op)
                       (= (get instruction-keysets op) (set (keys instruction))))
          (reject! :non-canonical-instruction instruction))
        (when (and (= :virtual registers)
                   (contains? #{:mir/spill-load :mir/spill-store :mir/move} op))
          (reject! :physical-operation-in-virtual-program instruction))
        (when (and (contains? #{:mir/reentry :mir/recur} op)
                   (or (= :virtual registers) (not= :aarch64 target)
                       (not= 3 version)))
          (reject! :direct-reentry-profile-violation instruction))
        (when (and (= :virtual registers)
                   (contains? #{:mir/multiply-add :mir/multiply-subtract} op))
          (reject! :target-selected-operation-in-virtual-program instruction))
        (when (and (= :mir/branch-nonzero op) (not= :aarch64 target))
          (reject! :target-selected-operation-target-mismatch instruction))
        (doseq [register (concat
                          (keep instruction [:mir/dst :mir/src :mir/input
                                             :mir/left :mir/right :mir/addend :mir/test
                                             :mir/base :mir/length
                                             :mir/stored :mir/offset :mir/size])
                          (when (vector? (:mir/arguments instruction))
                            (:mir/arguments instruction))
                          (when (vector? (:mir/parameters instruction))
                            (:mir/parameters instruction)))]
          (when-not (register? register)
            (reject! :register-profile-violation instruction)))
        (when (and (contains? #{:mir/kernel-load-u8 :mir/kernel-store-u8
                                :mir/kernel-load-u32 :mir/kernel-store-u32
                                :mir/kernel-try-lock-u32 :mir/kernel-unlock-u32} op)
                   (not (register? (:mir/index instruction))))
          (reject! :register-profile-violation instruction))
        (when (contains? #{:mir/kernel-load-u8 :mir/kernel-store-u8} op)
          (when-not (and (contains? #{512 4096 16384} (:mir/maximum instruction))
                         (not (and (= :mir/kernel-store-u8 op)
                                   (= 16384 (:mir/maximum instruction)))))
            (reject! :invalid-kernel-memory-maximum instruction)))
        (when (contains? #{:mir/kernel-load-u32 :mir/kernel-store-u32} op)
          (when-not (= 512 (:mir/maximum instruction))
            (reject! :invalid-kernel-memory-maximum instruction)))
        (when (contains? #{:mir/kernel-try-lock-u32 :mir/kernel-unlock-u32} op)
          (when-not (= 4096 (:mir/maximum instruction))
            (reject! :invalid-kernel-memory-maximum instruction)))
        (when (and (= op :mir/return) (not (register? (:mir/value instruction))))
          (reject! :register-profile-violation instruction))
        (when (= op :mir/phi)
          (when (= :physical registers)
            (reject! :phi-in-physical-program instruction))
          (when-not (and (vector? (:mir/incomings instruction))
                         (every? (fn [incoming]
                                   (and (map? incoming)
                                        (= #{:mir/predecessor :mir/value}
                                           (set (keys incoming)))
                                        (gmir/label? (:mir/predecessor incoming))
                                        (register? (:mir/value incoming))))
                                 (:mir/incomings instruction)))
            (reject! :invalid-phi-incomings instruction)))
        (when (contains? #{:mir/call :mir/tail-call} op)
          (when-not (and (= 3 version)
                         (gmir/function-id? (:mir/callee instruction))
                         (vector? (:mir/arguments instruction))
                         (<= (count (:mir/arguments instruction)) 5))
            (reject! :invalid-call instruction))
          (when (= :physical registers)
            (when-not (and (or (= op :mir/tail-call)
                               (= (:mir/dst instruction)
                                  (get return-registers target)))
                           (= (:mir/arguments instruction)
                              (subvec (get call-argument-registers target)
                                      0 (count (:mir/arguments instruction)))))
              (reject! :physical-call-profile-violation instruction))))
        (when (= :mir/reentry op)
          (when-not (and (vector? (:mir/parameters instruction))
                         (<= (count (:mir/parameters instruction)) 5))
            (reject! :invalid-direct-reentry instruction)))
        (when (= :mir/recur op)
          (when-not (and (vector? (:mir/arguments instruction))
                         (<= (count (:mir/arguments instruction)) 5))
            (reject! :invalid-direct-recur instruction)))
        (when (= op :mir/runtime-call)
          (let [runtime (:mir/runtime instruction)
                arguments (:mir/arguments instruction)
                expected (get gmir/runtime-operation-arities runtime ::missing)]
            (when-not (and (not= ::missing expected)
                           (= expected (count arguments))
                           (= (get runtime-context-offsets runtime)
                              (:mir/context-offset instruction)))
              (reject! :invalid-runtime-call instruction))
            (when (= :physical registers)
              (when-not (and (= (:mir/dst instruction)
                                (get return-registers target))
                             (= arguments
                                (subvec (get runtime-argument-registers target)
                                        0 (count arguments))))
                (reject! :physical-runtime-call-profile-violation instruction)))))
        (when (= op :mir/x86-privileged)
          (let [action (:mir/action instruction)
                arguments (:mir/arguments instruction)
                expected (get gmir/x86-privileged-action-arities action ::missing)]
            (when-not (and (= :x86-64 target)
                           (not= ::missing expected)
                           (= expected (count arguments)))
              (reject! :invalid-x86-privileged instruction))))
        (when (= op :mir/capability-call)
          (let [kind (:mir/kind instruction)
                capability (:mir/capability instruction)
                arguments (:mir/arguments instruction)]
            (when-not (and (contains? gmir/capability-kinds kind)
                           (integer? capability) (<= 0 capability 255)
                           (= 1 (count arguments))
                           (= (get capability-context-offsets kind)
                              (:mir/context-offset instruction)))
              (reject! :invalid-capability-call instruction))
            (when (= :physical registers)
              (when-not (and (= (:mir/dst instruction)
                                (get return-registers target))
                             (= arguments
                                (get-in capability-argument-registers
                                        [target kind])))
                (reject! :physical-capability-call-profile-violation
                         instruction)))))
        (when (and (= op :mir/constant)
                   (not (gmir/i64-value? (:mir/value instruction))))
          (reject! :constant-not-i64 instruction))
        (when (and (= op :mir/quotient-constant)
                   (not (gmir/i64-value? (:mir/divisor instruction))))
          (reject! :constant-divisor-not-i64 instruction))
        (when (and (= op :mir/data-address)
                   (not (string? (:mir/content instruction))))
          (reject! :invalid-data-content instruction))
        (when (and (= op :mir/argument)
                   (not (and (integer? (:mir/index instruction))
                             (not (neg? (:mir/index instruction))))))
          (reject! :argument-index-invalid instruction))
        (when (contains? #{:mir/spill-load :mir/spill-store} op)
          (when-not (and (integer? (:mir/slot instruction))
                         (some? frame-slots)
                         (<= 0 (:mir/slot instruction))
                         (< (:mir/slot instruction) frame-slots))
            (reject! :spill-slot-invalid instruction)))
        (when (contains? #{:mir/label :mir/branch-zero :mir/branch-nonzero
                           :mir/jump} op)
          (let [id (if (= op :mir/label) (:mir/id instruction) (:mir/target instruction))]
            (when-not (gmir/label? id)
              (reject! :invalid-label instruction))))))
    (let [labels (map :mir/id (filter #(= :mir/label (:mir/op %)) instructions))
          label-set (set labels)
          targets (keep :mir/target instructions)]
      (when-not (= (count labels) (count label-set))
        (reject! :duplicate-label {:labels labels}))
      (doseq [branch-target targets]
        (when-not (contains? label-set branch-target)
          (reject! :unresolved-target {:target branch-target})))
      (when (and (= 2 version) (= :virtual registers))
        (gmir/validate!
         {:gmir/version 2
          :gmir/instructions
          (mapv (fn [instruction]
                  (reduce-kv
                   (fn [out key value]
                     (if (= key :mir/context-offset)
                       out
                       (assoc out
                              (case key
                                :mir/op :gmir/op
                                :mir/dst :gmir/dst
                                :mir/index :gmir/index
                                :mir/value :gmir/value
                                :mir/left :gmir/left
                                :mir/right :gmir/right
                                :mir/id :gmir/id
                                :mir/test :gmir/test
                                :mir/target :gmir/target
                                :mir/incomings :gmir/incomings
                                :mir/content :gmir/content
                                :mir/runtime :gmir/runtime
                                :mir/capability :gmir/capability
                                :mir/kind :gmir/kind
                                :mir/arguments :gmir/arguments)
                              (cond
                                (= key :mir/op) (keyword "gmir" (name value))
                                (= key :mir/incomings)
                                (mapv (fn [incoming]
                                        {:gmir/predecessor (:mir/predecessor incoming)
                                         :gmir/value (:mir/value incoming)})
                                      value)
                                :else value))))
                   {} instruction))
                instructions)}))))
  program)

(defn- valid-direct-reentry-prefix?
  "The reentry marker is meaningful only after the public ABI arguments have
  been materialized into the homes it names. Symbolically execute the closed
  entry transport language so malformed external MIR cannot place the marker
  before a required move (or name a home containing another parameter)."
  [target arity instructions reentry-index parameters]
  (let [abi (subvec (get call-argument-registers target) 0 arity)
        argument-prefix (subvec instructions 0 (min arity (count instructions)))
        canonical-arguments?
        (and (= arity (count argument-prefix))
             (= (vec (range arity)) (mapv :mir/index argument-prefix))
             (= abi (mapv :mir/dst argument-prefix))
             (every? #(= :mir/argument (:mir/op %)) argument-prefix))]
    (when (and canonical-arguments? (<= arity reentry-index))
      (let [initial {:registers (zipmap abi (range arity)) :slots {}}
            result
            (reduce
             (fn [state {:mir/keys [op dst src slot]}]
               (if (= ::invalid state)
                 (reduced state)
                 (case op
                   :mir/move
                   (if (contains? (:registers state) src)
                     (assoc-in state [:registers dst] (get-in state [:registers src]))
                     (reduced ::invalid))

                   :mir/spill-store
                   (if (contains? (:registers state) src)
                     (assoc-in state [:slots slot] (get-in state [:registers src]))
                     (reduced ::invalid))

                   :mir/spill-load
                   (if (contains? (:slots state) slot)
                     (assoc-in state [:registers dst] (get-in state [:slots slot]))
                     (reduced ::invalid))

                   (reduced ::invalid))))
             initial
             (subvec instructions arity reentry-index))]
        (and (not= ::invalid result)
             (= (vec (range arity))
                (mapv #(get-in result [:registers %]) parameters)))))))

(defn- validate-v3-module!
  [{:mir/keys [target registers entry functions] :as module}]
  (when-not (and (= #{:mir/version :mir/target :mir/registers
                      :mir/entry :mir/functions}
                    (set (keys module)))
                 (contains? targets target)
                 (contains? #{:virtual :physical} registers)
                 (gmir/function-id? entry)
                 (vector? functions)
                 (seq functions))
    (reject! :non-canonical-module module))
  (let [names (mapv :mir/name functions)
        signatures (into {} (map (juxt :mir/name :mir/arity) functions))]
    (when-not (and (every? gmir/function-id? names)
                   (= (count names) (count (distinct names)))
                   (contains? signatures entry))
      (reject! :invalid-module-functions {:entry entry :names names}))
    (doseq [{:mir/keys [name arity frame-slots frame-policy instructions]
             :as function} functions]
      (let [expected-keys (if (= :virtual registers)
                            #{:mir/name :mir/arity :mir/instructions}
                            #{:mir/name :mir/arity :mir/frame-slots
                              :mir/frame-policy :mir/instructions})
            calls (filter #(or (call-operation? (:mir/op %))
                               (= :mir/recur (:mir/op %)))
                          instructions)
            direct-calls (filter #(contains? #{:mir/call :mir/tail-call}
                                              (:mir/op %)) instructions)]
        (when-not (and (= expected-keys (set (keys function)))
                       (gmir/function-id? name)
                       (integer? arity) (<= 0 arity 5)
                       (or (= :virtual registers)
                           (contains? #{:allocator :all-vregs :call-live}
                                      frame-policy)))
          (reject! :non-canonical-function function))
        (validate-flat!
         (cond-> {:mir/version 3 :mir/target target :mir/registers registers
                  :mir/instructions instructions}
           (= :physical registers) (assoc :mir/frame-slots frame-slots)))
        (when (= :physical registers)
          (let [arguments (filterv #(= :mir/argument (:mir/op %)) instructions)
                expected-registers (subvec (get call-argument-registers target)
                                           0 arity)]
            (when-not (and (= arity (count arguments))
                           (= (vec (range arity)) (mapv :mir/index arguments))
                           (= expected-registers (mapv :mir/dst arguments)))
              (reject! :entry-argument-profile-violation
                       {:function name :arguments arguments}))))
        (when (and (= :physical registers)
                   (if (seq calls)
                     (not (contains? #{:all-vregs :call-live} frame-policy))
                     (not= :allocator frame-policy)))
          (reject! :call-frame-policy-violation function))
        (when (= :physical registers)
          (let [reentries (filterv #(= :mir/reentry (:mir/op %)) instructions)
                recurs (filterv #(= :mir/recur (:mir/op %)) instructions)
                reentry-index (first (keep-indexed
                                      #(when (= :mir/reentry (:mir/op %2)) %1)
                                      instructions))
                recur-terminates?
                (every? (fn [[index instruction]]
                          (if (= :mir/recur (:mir/op instruction))
                            (let [next-instruction (get instructions (inc index))]
                              (or (nil? next-instruction)
                                  (= :mir/label (:mir/op next-instruction))))
                            true))
                        (map-indexed vector instructions))]
            (when-not (if (seq recurs)
                        (and (= :aarch64 target)
                             (= 1 (count reentries))
                             (= arity (count (:mir/parameters (first reentries))))
                             (= arity
                                (count (distinct
                                        (:mir/parameters (first reentries)))))
                             (valid-direct-reentry-prefix?
                              target arity instructions reentry-index
                              (:mir/parameters (first reentries)))
                             recur-terminates?
                             (every? #(= (:mir/parameters (first reentries))
                                         (:mir/arguments %))
                                     recurs))
                        (empty? reentries))
              (reject! :invalid-direct-reentry-contract function))))
        (when (and (= :physical registers) (= :all-vregs frame-policy))
          (let [value-ops #{:mir/argument :mir/constant :mir/add :mir/subtract
                            :mir/multiply :mir/quotient :mir/quotient-constant
                            :mir/bit-and :mir/bit-or
                            :mir/bit-xor :mir/shift-left :mir/shift-right-signed
                            :mir/shift-right-unsigned
                            :mir/f64-add :mir/f64-subtract :mir/f64-multiply
                            :mir/f64-divide :mir/f64-min :mir/f64-max
                            :mir/f64-sqrt :mir/f64-equal :mir/f64-less-than
                            :mir/f64-less-or-equal :mir/f64-greater-than
                            :mir/f64-greater-or-equal :mir/f64-unordered
                            :mir/kernel-load-u8 :mir/kernel-store-u8
                            :mir/kernel-load-u32 :mir/kernel-store-u32
                            :mir/kernel-try-lock-u32 :mir/kernel-unlock-u32
                            :mir/kernel-subregion
                            :mir/equal :mir/less-than
                            :mir/greater-than :mir/less-or-equal
                            :mir/greater-or-equal :mir/call :mir/runtime-call
                            :mir/capability-call :mir/x86-privileged
                            :mir/data-address}]
            (doseq [[index instruction] (map-indexed vector instructions)
                    :when (contains? value-ops (:mir/op instruction))]
              (let [store (get instructions (inc index))]
                (when-not (and (= :mir/spill-store (:mir/op store))
                               (= (:mir/dst instruction) (:mir/src store)))
                  (reject! :unbacked-call-frame-value
                           {:function name :instruction instruction}))))
            (doseq [[index {:mir/keys [arguments] :as call}]
                    (map-indexed vector instructions)
                    :when (call-operation? (:mir/op call))]
              (let [loads (when (>= index (count arguments))
                            (subvec instructions (- index (count arguments)) index))]
                (when-not (and (some? loads)
                               (= (count loads) (count arguments))
                               (every? #(= :mir/spill-load (:mir/op %)) loads)
                               (= arguments (mapv :mir/dst loads)))
                  (reject! :non-parallel-call-arguments
                           {:function name :call call}))))))
        (doseq [{:mir/keys [callee arguments] :as call} direct-calls]
          (let [callee-arity (get signatures callee ::missing)]
            (when (= ::missing callee-arity)
              (reject! :unresolved-callee call))
            (when-not (= callee-arity (count arguments))
              (reject! :call-arity-mismatch
                       {:function name :call call :expected callee-arity})))))))
  module)

(defn validate!
  "Validate virtual or physical MIR and return it unchanged. v3 modules own
  independent function frames and a closed scalar direct-call graph."
  [{:mir/keys [version] :as program}]
  (if (= 3 version)
    (validate-v3-module! program)
    (validate-flat! program)))

(defn- select-instruction [target instruction]
  (reduce-kv
   (fn [out key value]
     (assoc out
            (case key
              :gmir/op :mir/op
              :gmir/dst :mir/dst
              :gmir/index :mir/index
              :gmir/value :mir/value
              :gmir/input :mir/input
              :gmir/left :mir/left
              :gmir/right :mir/right
              :gmir/id :mir/id
              :gmir/test :mir/test
              :gmir/target :mir/target
              :gmir/incomings :mir/incomings
              :gmir/content :mir/content
              :gmir/callee :mir/callee
              :gmir/runtime :mir/runtime
              :gmir/action :mir/action
              :gmir/capability :mir/capability
              :gmir/kind :mir/kind
              :gmir/arguments :mir/arguments
              :gmir/base :mir/base
              :gmir/length :mir/length
              :gmir/stored :mir/stored
              :gmir/offset :mir/offset
              :gmir/size :mir/size
              :gmir/maximum :mir/maximum)
            (cond
              (= key :gmir/op) (keyword "mir" (name value))
              (= key :gmir/incomings)
              (mapv (fn [incoming]
                      {:mir/predecessor (:gmir/predecessor incoming)
                       :mir/value (:gmir/value incoming)})
                    value)
              :else value)))
   (case (:gmir/op instruction)
     :gmir/runtime-call
     {:mir/context-offset (get runtime-context-offsets
                                (:gmir/runtime instruction))}
     :gmir/capability-call
     {:mir/context-offset (get capability-context-offsets
                                (:gmir/kind instruction))}
     {})
   instruction))

(defn- instruction-sources [instruction]
  (concat (keep instruction [:mir/src :mir/input :mir/left :mir/right :mir/addend
                             :mir/test :mir/value :mir/base :mir/length
                             :mir/stored :mir/offset :mir/size])
          (when (vector? (:mir/incomings instruction))
            (map :mir/value (:mir/incomings instruction)))
          (when (contains? #{:mir/kernel-load-u8 :mir/kernel-store-u8
                             :mir/kernel-load-u32 :mir/kernel-store-u32
                             :mir/kernel-try-lock-u32 :mir/kernel-unlock-u32}
                           (:mir/op instruction))
            [(:mir/index instruction)])
          (when (vector? (:mir/arguments instruction))
            (:mir/arguments instruction))))

(def ^:private schedulable-integer-operations
  "Pure, non-trapping integer operations admitted to local scheduling. Every
  other operation is a hard barrier: in particular constants, memory, calls,
  division, labels, terminators, phi transport, and target-selected ops."
  #{:mir/add :mir/subtract :mir/multiply
    :mir/bit-and :mir/bit-or :mir/bit-xor
    :mir/shift-left :mir/shift-right-signed :mir/shift-right-unsigned
    :mir/equal :mir/less-than :mir/greater-than
    :mir/less-or-equal :mir/greater-or-equal})

(def ^:private scheduling-latencies
  "Portable scheduling heuristic, not a microarchitecture benchmark. The
  target key keeps policy explicit as the profiles diverge; both current
  profiles conservatively model integer multiply as the only multi-cycle op."
  {:x86-64 {:mir/multiply 3}
   :aarch64 {:mir/multiply 3}})

(defn- scheduling-latency [target instruction]
  (get-in scheduling-latencies [target (:mir/op instruction)] 1))

(defn- scheduling-register? [target value]
  (or (gmir/vreg? value) (physical-register? target value)))

(defn- segment-predecessors [target instructions]
  "Register dependencies within one scheduling segment. SSA vregs need RAW
  edges only, but post-allocation physical registers are reused: preserve WAR
  and WAW order too, or a later definition can move before an earlier read or
  an earlier definition can move after the value meant to replace it."
  (loop [index 0
         last-def {}
         readers-since-def {}
         preds []]
    (if (= index (count instructions))
      preds
      (let [instruction (nth instructions index)
            sources (->> (instruction-sources instruction)
                         (filter #(scheduling-register? target %))
                         set)
            dst (:mir/dst instruction)
            register-dst? (scheduling-register? target dst)
            raw-preds (keep last-def sources)
            ;; Capture anti-dependencies before recording this instruction as
            ;; a reader. A read-modify-write reads the old value and defines
            ;; the new value atomically; it must not depend on itself.
            war-preds (when register-dst? (get readers-since-def dst))
            waw-pred (when register-dst? (get last-def dst))
            pred-indexes (cond-> (into (set raw-preds) war-preds)
                           (some? waw-pred) (conj waw-pred))
            readers-since-def
            (reduce #(update %1 %2 (fnil conj #{}) index)
                    readers-since-def sources)
            readers-since-def (if register-dst?
                                (assoc readers-since-def dst #{})
                                readers-since-def)
            last-def (if register-dst? (assoc last-def dst index) last-def)]
        (recur (inc index) last-def readers-since-def
               (conj preds pred-indexes))))))

(defn- segment-ready-at-cycle? [predecessors completion cycle index]
  (every? #(and (contains? completion %)
                (<= (get completion %) cycle))
          (nth predecessors index)))

(defn- segment-order-positions [order-indices]
  (into {}
        (map-indexed (fn [position original-index]
                       [original-index position])
                     order-indices)))

(defn- valid-scheduled-segment?
  "True when ORDER-INDICES is an exact, register-dependency-respecting
  permutation of the original integer indexes in INSTRUCTIONS."
  [target instructions order-indices]
  (let [instruction-count (count instructions)]
    (and (= instruction-count (count order-indices))
         (every? integer? order-indices)
         (= (frequencies order-indices)
            (zipmap (range instruction-count) (repeat 1)))
         (let [predecessors (segment-predecessors target instructions)
               positions (segment-order-positions order-indices)]
           (every? (fn [index]
                     (every? #(< (positions %)
                                 (positions index))
                             (nth predecessors index)))
                   (range instruction-count))))))

(defn- verify-scheduled-segment!
  [target instructions order-indices]
  (when-not (valid-scheduled-segment? target instructions order-indices)
    (reject! :schedule-violates-register-dependencies
             {:segment instructions :scheduled-indexes order-indices}))
  order-indices)

(defn- segment-completion-times
  "Modeled completion cycles for an explicit permutation of original integer
  instruction indexes. This is a portable structural score, not wall-clock
  performance evidence."
  [target instructions order-indices]
  (verify-scheduled-segment! target instructions order-indices)
  (let [predecessors (segment-predecessors target instructions)
        instruction-count (count instructions)]
    (loop [cycle 0
           order-position 0
           completion {}
           times (vec (repeat instruction-count 0))]
      (if (= order-position instruction-count)
        times
        (let [index (nth order-indices order-position)]
          (if (segment-ready-at-cycle? predecessors completion cycle index)
            (let [done (+ cycle
                          (scheduling-latency target
                                              (nth instructions index)))]
              (recur (inc cycle)
                     (inc order-position)
                     (assoc completion index done)
                     (assoc times index done)))
            (recur (inc cycle) order-position completion times)))))))

(defn- segment-sum-completion-times
  [target instructions order-indices]
  (reduce + (segment-completion-times target instructions order-indices)))

(defn- schedule-integer-segment-indices
  "Return a deterministic dependency-aware permutation of original indexes."
  [target instructions]
  (if (< (count instructions) 2)
    (vec (range (count instructions)))
    (let [predecessors (segment-predecessors target instructions)
          successors
          (reduce-kv (fn [out index inputs]
                       (reduce #(update %1 %2 conj index) out inputs))
                     (vec (repeat (count instructions) #{}))
                     predecessors)
          heights
          (reduce (fn [out index]
                    (assoc out index
                           (+ (scheduling-latency target (nth instructions index))
                              (reduce max 0 (map #(nth out %) (nth successors index))))))
                  (vec (repeat (count instructions) 0))
                  (reverse (range (count instructions))))]
      (verify-scheduled-segment!
       target
       instructions
       (loop [cycle 0
              remaining (set (range (count instructions)))
              completion {}
              out []]
         (if (empty? remaining)
           out
           (let [ready (->> remaining
                            (filter (fn [index]
                                      (segment-ready-at-cycle? predecessors
                                                                 completion
                                                                 cycle
                                                                 index)))
                            (sort-by (fn [index] [(- (nth heights index)) index]))
                            first)]
             (if (nil? ready)
               (recur (inc cycle) remaining completion out)
               (recur (inc cycle)
                      (disj remaining ready)
                      (assoc completion ready
                             (+ cycle
                                (scheduling-latency target
                                                    (nth instructions ready))))
                      (conj out ready))))))))))

(defn- schedule-integer-segment
  "Deterministic dependency-aware list scheduling for one barrier-free SSA
  segment. Critical-path height breaks ties first, original position second.
  A conceptual issue cycle lets independent work fill modeled dependency
  latency without inserting machine instructions or claiming wall-clock gain."
  [target instructions]
  (mapv #(nth instructions %)
        (schedule-integer-segment-indices target instructions)))

(defn- aarch64-fusion-pair?
  "True when INDEX and INDEX+1 are an already-adjacent multiply/add pair the
  downstream AArch64 selector can turn into one MADD/MSUB. Keep such pairs
  fixed: separating them would regress code quality before MC fusion runs."
  [target instructions use-counts index]
  (let [multiply (nth instructions index nil)
        consumer (nth instructions (inc index) nil)
        product (:mir/dst multiply)
        consumer-op (:mir/op consumer)
        consumes-product?
        (or (and (= :mir/add consumer-op)
                 (or (= product (:mir/left consumer))
                     (= product (:mir/right consumer))))
            (and (= :mir/subtract consumer-op)
                 (= product (:mir/right consumer))))]
    (and (= :mir/multiply (:mir/op multiply))
         (scheduling-register? target product)
         (= 1 (get use-counts product))
         consumes-product?)))

(defn- protected-scheduling-indexes [target instructions]
  (if-not (= :aarch64 target)
    #{}
    (let [use-counts (frequencies (filter #(scheduling-register? target %)
                                          (mapcat instruction-sources instructions)))]
      (reduce (fn [out index]
                (if (aarch64-fusion-pair? target instructions use-counts index)
                  (conj out index (inc index))
                  out))
              #{}
              (range (max 0 (dec (count instructions))))))))

(defn- schedule-instructions
  "Schedule only consecutive pure integer segments. Barriers retain their
  exact position relative to all surrounding segments. Labels, branches,
  spills, moves, and calls are barriers, so each basic block is scheduled
  independently once register allocation has fixed physical identities."
  [target instructions]
  (let [protected (protected-scheduling-indexes target instructions)]
    (letfn [(flush-segment [out segment]
              (into out (schedule-integer-segment target segment)))]
      (let [{:keys [out segment]}
            (reduce (fn [{:keys [out segment]} instruction]
                      (let [index (+ (count out) (count segment))]
                        (if (and (not (contains? protected index))
                                 (contains? schedulable-integer-operations
                                            (:mir/op instruction)))
                          {:out out :segment (conj segment instruction)}
                          {:out (conj (flush-segment out segment) instruction)
                           :segment []})))
                    {:out [] :segment []}
                    instructions)]
        (flush-segment out segment)))))

(defn- schedule-program [{:mir/keys [target] :as program}]
  (update program :mir/instructions #(schedule-instructions target %)))

(defn- aarch64-fuse-zero-equality-branches
  "Turn one SSA-only `zero; equal; branch-zero` triple into branch-nonzero.

  Both removed definitions must have exactly one use in the complete function,
  including phi incoming edges. Exact adjacency excludes labels and other
  control-flow boundaries. This runs before physical allocation, where vreg
  identity still makes global use counts meaningful."
  [target instructions]
  (if-not (= :aarch64 target)
    (vec instructions)
    (let [instructions (vec instructions)
          use-counts (frequencies
                      (filter gmir/vreg?
                              (mapcat instruction-sources instructions)))]
      (loop [index 0, out []]
        (if (>= index (count instructions))
          (vec out)
          (let [constant (get instructions index)
                equal (get instructions (inc index))
                branch (get instructions (+ index 2))
                zero (:mir/dst constant)
                result (:mir/dst equal)
                left (:mir/left equal)
                right (:mir/right equal)
                operand (cond (= zero left) right
                              (= zero right) left)
                fuse? (and (= :mir/constant (:mir/op constant))
                           (zero? (:mir/value constant))
                           (= :mir/equal (:mir/op equal))
                           (= :mir/branch-zero (:mir/op branch))
                           (= result (:mir/test branch))
                           (gmir/vreg? operand)
                           (= 3 (count (set [zero result operand])))
                           (= 1 (get use-counts zero))
                           (= 1 (get use-counts result)))]
            (if fuse?
              (recur (+ index 3)
                     (conj out {:mir/op :mir/branch-nonzero
                                :mir/test operand
                                :mir/target (:mir/target branch)}))
              (recur (inc index) (conj out constant)))))))))

(defn- select-instructions
  "Select one function while retaining SSA constants long enough to choose a
  target-independent constant-divisor operation. A divisor vreg disappears
  from the closed operation after its literal value is captured. Its constant
  definition is removed only when no other selected instruction consumes it."
  [target instructions constant-division?]
  (let [{:keys [out specialized-divisors]}
        (reduce
         (fn [{:keys [constants out specialized-divisors]} instruction]
           (let [right (:gmir/right instruction)
                 specialized? (and constant-division?
                                   (= :gmir/quotient (:gmir/op instruction))
                                   (contains? constants right))
                 selected (select-instruction target instruction)
                 selected (if specialized?
                            (-> selected
                                (assoc :mir/op :mir/quotient-constant
                                       :mir/divisor (get constants right))
                                (dissoc :mir/right))
                            selected)
                 constants (if (= :gmir/constant (:gmir/op instruction))
                             (assoc constants (:gmir/dst instruction)
                                    (:gmir/value instruction))
                             constants)]
             {:constants constants
              :specialized-divisors (cond-> specialized-divisors
                                      specialized? (conj right))
              :out (conj out selected)}))
         {:constants {} :specialized-divisors #{} :out []}
         instructions)
        ;; NBB represents admitted i64 literals as JavaScript BigInt values.
        ;; They are not SSA identities and must not enter a CLJS hash-set
        ;; (which would attempt object identity bookkeeping on a primitive).
        out (aarch64-fuse-zero-equality-branches target out)
        live-sources (->> out
                          (mapcat instruction-sources)
                          (filter gmir/vreg?)
                          set)]
    (->> out
         (remove (fn [{:mir/keys [op dst]}]
                   (and (= :mir/constant op)
                        (contains? specialized-divisors dst)
                        (not (contains? live-sources dst)))))
         vec)))

(defn select-target
  "Select the closed GMIR operation set into target MIR, preserving vregs."
  [target program]
  (when-not (contains? targets target)
    (reject! :unsupported-target {:target target}))
  (gmir/validate! program)
  (let [instructions (if (= 3 (:gmir/version program))
                       (mapcat :gmir/instructions (:gmir/functions program))
                       (:gmir/instructions program))
        privileged (filter #(= :gmir/x86-privileged (:gmir/op %)) instructions)]
    (when (and (not= :x86-64 target) (seq privileged))
      (reject! :x86-privileged-target-mismatch
               {:target target :actions (mapv :gmir/action privileged)})))
  (validate!
   (if (= 3 (:gmir/version program))
     {:mir/version 3
      :mir/target target
      :mir/registers :virtual
      :mir/entry (:gmir/entry program)
      :mir/functions
      (mapv (fn [{:gmir/keys [name arity instructions]}]
              {:mir/name name :mir/arity arity
               :mir/instructions (select-instructions target instructions true)})
            (:gmir/functions program))}
     {:mir/version (:gmir/version program)
      :mir/target target
      :mir/registers :virtual
      :mir/instructions (mapv #(select-instruction target %)
                              (:gmir/instructions program))})))

(defn- sources [instruction]
  (instruction-sources instruction))

(defn- preceding-label [instructions index]
  (loop [cursor (dec index)]
    (when (not (neg? cursor))
      (let [instruction (nth instructions cursor)]
        (cond
          (= :mir/label (:mir/op instruction)) (:mir/id instruction)
          (= :mir/phi (:mir/op instruction)) (recur (dec cursor))
          :else nil)))))

(defn- lower-phis
  [{:mir/keys [instructions] :as program}]
  (let [phis (->> instructions
                  (map-indexed vector)
                  (filter (fn [[_ instruction]] (= :mir/phi (:mir/op instruction))))
                  vec)
        slot-by-dst (into {} (map-indexed (fn [slot [_ instruction]]
                                           [(:mir/dst instruction) slot])
                                         phis))
        stores-by-edge
        (reduce (fn [stores [index {:mir/keys [dst incomings]}]]
                  (let [join (preceding-label instructions index)
                        slot (get slot-by-dst dst)]
                    (reduce (fn [out incoming]
                              (update out [(:mir/predecessor incoming) join]
                                      (fnil conj [])
                                      {:mir/op :mir/merge-store
                                       :mir/src (:mir/value incoming)
                                       :mir/slot slot}))
                            stores incomings)))
                {} phis)
        lowered
        (:out
         (reduce (fn [{:keys [label out]} {:mir/keys [op target dst] :as instruction}]
                   (case op
                     :mir/label {:label (:mir/id instruction)
                                 :out (conj out instruction)}
                     :mir/phi {:label label
                               :out (conj out {:mir/op :mir/merge-load
                                              :mir/dst dst
                                              :mir/slot (get slot-by-dst dst)})}
                     :mir/jump {:label label
                                :out (into out
                                           (concat (get stores-by-edge [label target] [])
                                                   [instruction]))}
                     {:label label :out (conj out instruction)}))
                 {:label nil :out []}
                 instructions))]
    {:program (assoc program :mir/instructions (vec lowered))
     :merge-slots (count phis)
     :merge-dst-by-slot (into {} (map-indexed (fn [slot [_ instruction]]
                                                [slot (:mir/dst instruction)])
                                              phis))}))

(def ^:private parallel-copy-temp ::parallel-copy-temp)

(defn- remove-at [values index]
  (into (subvec values 0 index) (subvec values (inc index))))

(defn- schedule-parallel-copies
  "Lower simultaneous physical-register copies deterministically. Acyclic
  copies become moves. A cycle is broken with one reusable frame slot."
  [copies temp-slot]
  (loop [pending (vec (remove #(= (:mir/dst %) (:mir/src %)) copies))
         out []
         used-temp? false]
    (if (empty? pending)
      {:instructions out :used-temp? used-temp?}
      (let [pending-sources (set (map :mir/src pending))
            ready-index (first
                         (keep-indexed
                          (fn [index {:mir/keys [dst]}]
                            (when-not (contains? pending-sources dst) index))
                          pending))]
        (if (some? ready-index)
          (let [{:mir/keys [dst src]} (nth pending ready-index)
                instruction (if (= parallel-copy-temp src)
                              {:mir/op :mir/spill-load
                               :mir/dst dst
                               :mir/slot temp-slot}
                              {:mir/op :mir/move :mir/dst dst :mir/src src})]
            (recur (remove-at pending ready-index)
                   (conj out instruction)
                   used-temp?))
          (let [{:mir/keys [src]} (first pending)]
            (recur (mapv (fn [copy]
                           (if (= src (:mir/src copy))
                             (assoc copy :mir/src parallel-copy-temp)
                             copy))
                         pending)
                   (conj out {:mir/op :mir/spill-store
                              :mir/src src
                              :mir/slot temp-slot})
                   true)))))))

(defn- coalesce-phi-transports
  "Replace complete edge merge-store groups and their join loads with a
  deterministic parallel-copy schedule. Invalid or incomplete groups retain
  the frame-backed representation instead of being partially rewritten."
  [{:mir/keys [instructions frame-slots] :as program} merge-slots]
  (if (zero? merge-slots)
    program
    (let [loads-by-slot (group-by :mir/slot
                                  (filter #(and (= :mir/spill-load (:mir/op %))
                                                (< (:mir/slot %) merge-slots))
                                          instructions))
          stores-by-slot (group-by :mir/slot
                                   (filter #(and (= :mir/spill-store (:mir/op %))
                                                 (< (:mir/slot %) merge-slots))
                                           instructions))
          candidates (set (range merge-slots))
          complete? (every? #(and (= 1 (count (get loads-by-slot %)))
                                  (<= 2 (count (get stores-by-slot %))))
                            candidates)
          load-register (into {} (map (fn [slot]
                                        [slot (:mir/dst (first (get loads-by-slot slot)))])
                                      candidates))
          compact-slot (fn [slot]
                         (- slot (count (filter #(< % slot) candidates))))
          merge-store? #(and (= :mir/spill-store (:mir/op %))
                             (contains? candidates (:mir/slot %)))]
      (if-not complete?
        program
        (let [{:keys [out used-temp? valid?]}
              (loop [remaining instructions, out [], used-temp? false]
                (if-let [{:mir/keys [op slot] :as instruction} (first remaining)]
                  (cond
                    (merge-store? instruction)
                    (let [[stores tail] (split-with merge-store? remaining)]
                      (if (= :mir/jump (:mir/op (first tail)))
                        (let [copies (mapv (fn [{:mir/keys [src slot]}]
                                             {:mir/dst (get load-register slot)
                                              :mir/src src})
                                           stores)
                              scheduled (schedule-parallel-copies
                                         copies
                                         (- frame-slots (count candidates)))]
                          (recur tail
                                 (into out (:instructions scheduled))
                                 (or used-temp? (:used-temp? scheduled))))
                        {:out out :used-temp? used-temp? :valid? false}))

                    (and (= :mir/spill-load op) (contains? candidates slot))
                    (recur (next remaining) out used-temp?)

                    (contains? instruction :mir/slot)
                    (recur (next remaining)
                           (conj out (assoc instruction :mir/slot (compact-slot slot)))
                           used-temp?)

                    :else
                    (recur (next remaining) (conj out instruction) used-temp?))
                  {:out out :used-temp? used-temp? :valid? true}))]
          (if-not valid?
            program
            (validate-flat! (assoc program
                                   :mir/frame-slots (+ (- frame-slots (count candidates))
                                                       (if used-temp? 1 0))
                                   :mir/instructions (vec out)))))))))

(defn- instruction-def [instruction]
  (when (gmir/vreg? (:mir/dst instruction))
    (:mir/dst instruction)))

(def ^:private terminators
  #{:mir/jump :mir/branch-zero :mir/branch-nonzero :mir/return})

(defn- basic-blocks [instructions]
  (let [n (count instructions)
        leaders (sort
                 (into #{0}
                       (mapcat
                        (fn [index]
                          (let [op (:mir/op (nth instructions index))]
                            (cond
                              (= op :mir/label) [index]
                              (contains? terminators op)
                              (when (< (inc index) n) [(inc index)])
                              :else nil)))
                        (range n))))
        block-count (count leaders)]
    (mapv (fn [block-index]
            (let [start (nth leaders block-index)
                  end (if (< (inc block-index) block-count)
                        (dec (nth leaders (inc block-index)))
                        (dec n))]
              {:index block-index :start start :end end}))
          (range block-count))))

(defn- label-block-indexes [instructions blocks]
  (into {}
        (keep (fn [{:keys [index start]}]
                (when (= :mir/label (:mir/op (nth instructions start)))
                  [(:mir/id (nth instructions start)) index]))
              blocks)))

(defn- block-successors [instructions blocks label->block]
  (mapv (fn [{:keys [index end]}]
          (let [op (:mir/op (nth instructions end))]
            (cond
              (= op :mir/return) []
              (= op :mir/jump)
              [(get label->block (:mir/target (nth instructions end)))]
              (contains? #{:mir/branch-zero :mir/branch-nonzero} op)
              (vec (remove nil?
                           [(when (< (inc index) (count blocks)) (inc index))
                            (get label->block
                                 (:mir/target (nth instructions end)))]))
              (< (inc index) (count blocks)) [(inc index)]
              :else [])))
        blocks))

(defn- block-predecessors [successors]
  (let [block-count (count successors)]
    (reduce (fn [preds from]
              (reduce (fn [acc to]
                        (update acc to (fnil conj #{}) from))
                      preds
                      (nth successors from)))
            (vec (repeat block-count #{}))
            (range block-count))))

(defn- intersect-dominator-sets [sets]
  (if (empty? sets)
    #{}
    (let [[head & tail] sets]
      (reduce set/intersection head tail))))

(defn- cfg-dominator-sets [predecessors]
  (let [block-count (count predecessors)
        universe (set (range block-count))
        initial (mapv (fn [block-index]
                        (if (zero? block-index) #{0} universe))
                      (range block-count))]
    (loop [dom initial]
      (let [next-dom
            (mapv (fn [block-index]
                    (if (zero? block-index)
                      #{0}
                      (let [preds (seq (nth predecessors block-index))]
                        (if preds
                          (conj (intersect-dominator-sets
                                 (map #(nth dom %) preds))
                                block-index)
                          (nth dom block-index)))))
                  (range block-count))]
        (if (= next-dom dom)
          dom
          (recur next-dom))))))

(defn- cfg-immediate-dominators [dominators]
  (mapv (fn [block-index]
          (when (pos? block-index)
            (let [strict (disj (nth dominators block-index) block-index)]
              (first (filter (fn [candidate]
                               (not (some (fn [other]
                                            (and (not= other candidate)
                                                 (contains? (nth dominators other)
                                                            candidate)))
                                          strict)))
                             strict)))))
        (range (count dominators))))

(defn- cfg-dominates? [dominators dominator block-index]
  (contains? (nth dominators block-index) dominator))

(defn- cfg-dominator-analysis [instructions]
  (let [blocks (basic-blocks instructions)
        label->block (label-block-indexes instructions blocks)
        successors (block-successors instructions blocks label->block)
        predecessors (block-predecessors successors)
        dominators (cfg-dominator-sets predecessors)]
    {:blocks blocks
     :successors successors
     :predecessors predecessors
     :dominators dominators
     :immediate-dominators (cfg-immediate-dominators dominators)}))

(defn- block-use-def [instructions blocks]
  (mapv (fn [{:keys [start end]}]
          (reduce (fn [{:keys [uses defs]} index]
                    (let [instruction (nth instructions index)]
                      ;; Only reads before a local definition are live-in.
                      ;; Counting later reads makes loop-local temporaries look
                      ;; live across the back edge and lengthens their lifetime
                      ;; to the latch.
                      {:uses (into uses (remove defs
                                                (filter gmir/vreg?
                                                        (sources instruction))))
                       :defs (if-let [definition (instruction-def instruction)]
                               (conj defs definition)
                               defs)}))
                  {:uses #{} :defs #{}}
                  (range start (inc end))))
        blocks))

(defn- cfg-live-variables [instructions]
  (let [blocks (basic-blocks instructions)
        label->block (label-block-indexes instructions blocks)
        successors (block-successors instructions blocks label->block)
        use-def (block-use-def instructions blocks)
        block-count (count blocks)
        empty (vec (repeat block-count #{}))]
    (loop [live-in empty
           live-out empty]
      (let [next-out (mapv (fn [block-index]
                             (reduce into #{}
                                     (map #(nth live-in %) (nth successors block-index))))
                           (range block-count))
            next-in (mapv (fn [block-index]
                            (let [{:keys [uses defs]} (nth use-def block-index)
                                  out (nth next-out block-index)]
                              (into uses (remove defs out))))
                          (range block-count))]
        (if (and (= next-in live-in) (= next-out live-out))
          {:blocks blocks :live-in next-in :live-out next-out}
          (recur next-in next-out))))))

(defn- back-edge-block-ends [instructions blocks label->block]
  (into #{}
        (keep (fn [{:keys [index end]}]
                (let [op (:mir/op (nth instructions end))]
                  (when (contains? #{:mir/jump :mir/branch-zero
                                     :mir/branch-nonzero} op)
                    (let [target (:mir/target (nth instructions end))
                          target-block (get label->block target)]
                      (when (and (some? target-block) (<= target-block index))
                        end)))))
              blocks)))

(defn- cfg-last-uses [instructions]
  (let [textual (reduce-kv
                 (fn [uses index instruction]
                   (reduce #(assoc %1 %2 index) uses
                           (filter gmir/vreg? (sources instruction))))
                 {} instructions)
        blocks (basic-blocks instructions)
        label->block (label-block-indexes instructions blocks)
        {:keys [live-out]} (cfg-live-variables instructions)
        back-edges (back-edge-block-ends instructions blocks label->block)]
    (reduce (fn [uses block-index]
              (let [end (:end (nth blocks block-index))]
                (if (contains? back-edges end)
                  (reduce (fn [out value]
                            (assoc out value (max (get out value -1) end)))
                          uses
                          (nth live-out block-index))
                  uses)))
            textual
            (range (count blocks)))))

(defn- last-uses [instructions]
  (cfg-last-uses instructions))

(defn- ordered-vregs [values]
  (sort-by (fn [value] (or (:gmir/id value) (str value))) values))

(defn- use-indexes
  "Every instruction index at which VALUE is a source, in order."
  [instructions]
  (reduce-kv
   (fn [uses index instruction]
     (reduce (fn [indexes value]
               (update indexes value (fnil conj []) index))
             uses
             (distinct (filter gmir/vreg? (sources instruction)))))
   {} instructions))

(defn- direct-recur-home-candidates
  "Map a self-tail argument SSA value to its exact allocator-owned parameter
  home when that recur is the value's sole use.  A repeated argument is not a
  candidate: one producer cannot define two homes, and the parallel-copy
  scheduler must retain responsibility for duplicating it.  Register
  availability is checked separately at the producer, where interference is
  known."
  [instructions current-function parameter-homes indexes]
  (let [sites (->> instructions
                   (keep-indexed
                    (fn [index {:mir/keys [op callee arguments] :as instruction}]
                      (when (and (= :mir/tail-call op)
                                 (= current-function callee)
                                 (= (count arguments)
                                    (count parameter-homes)))
                        [index instruction])))
                   vec)]
    ;; Multiple recur sites need path-sensitive interference.  This deliberately
    ;; small slice fails closed until the allocator owns that proof.
    (if (= 1 (count sites))
      (let [[index {:mir/keys [arguments]}] (first sites)
            counts (frequencies arguments)]
        (reduce (fn [out [value home]]
                  (if (and (gmir/vreg? value)
                           (= 1 (get counts value))
                           (= [index] (get indexes value)))
                    (assoc out value home)
                    out))
                {}
                (map vector arguments parameter-homes)))
      {})))

(def ^:private direct-home-control-boundaries
  #{:mir/label :mir/jump :mir/branch-zero :mir/branch-nonzero
    :mir/return :mir/tail-call :mir/recur :mir/reentry})

(defn- straight-line-to-recur?
  "The suffix after a producer reaches its sole recur use without crossing a
  control-flow or call boundary.  Register interference is handled separately;
  this guard keeps the optimization local and fail-closed."
  [instructions producer-index recur-index]
  (every? (fn [instruction]
            (and (not (call-operation? (:mir/op instruction)))
                 (not (contains? direct-home-control-boundaries
                                 (:mir/op instruction)))))
          (subvec instructions (inc producer-index) recur-index)))

(defn- next-use-of [indexes index value]
  (some (fn [use]
          (when (>= use index) use))
        (get indexes value)))

(defn- furthest-victim
  "The assigned value with the furthest next use, excluding PROTECTED
  operands. Ties keep the earlier ordered-vregs entry so the choice does
  not depend on hash-map iteration."
  [assigned indexes index protected]
  (let [candidates (filterv (fn [value]
                              (not (contains? protected value)))
                            (ordered-vregs (keys assigned)))]
    (when (seq candidates)
      (reduce (fn [best value]
                (let [best-use (or (next-use-of indexes index best) -1)
                      value-use (or (next-use-of indexes index value) -1)]
                  (if (> value-use best-use) value best)))
              (first candidates)
              (rest candidates)))))

(defn- expire-assigned
  "Remove VALUES from STATE's assignment without returning a register that is
  still owned by another SSA value (the latter occurs after a dying-left
  destination coalesces onto its source register).

  Freed registers return to the end of the free list, so a register is reused
  only after every other free one has been. That ordering is what the encoders'
  byte-exact expectations were written against, and it is why the pool grows on
  demand instead of being offered whole: handing out a wide pool up front makes
  a body needing three registers touch all of them, reach the preserved tier,
  and pay a save and a restore it never needed."
  [state values]
  (let [expired (vec (ordered-vregs values))
        assigned (:assigned state)
        remaining (apply dissoc assigned expired)
        still-owned (set (vals remaining))
        freed (remove still-owned (map assigned expired))]
    (-> state
        (assoc :assigned remaining)
        (update :free into freed))))

(defn- rebuild-pool-lists
  "Re-split POOL into the scratch free list and the reserve (leaf + preserved)
  after a call has clobbered every caller-saved register."
  [target pool assigned]
  (let [owned (set (vals assigned))
        scratch-count (count (get physical-registers target))]
    {:free (vec (remove owned (take scratch-count pool)))
     :reserve (vec (remove owned (drop scratch-count pool)))}))

(defn- expire-assigned-in-pool
  "Expire VALUES and restore the allocator's scratch/reserve partition.

  `expire-assigned` deliberately knows nothing about target register classes.
  Call-capable allocation must reclassify released preserved registers instead
  of appending them to the scratch list. Previously-used preserved registers go
  to the front of reserve: reusing one costs no additional frame save, while
  consuming a never-used preserved register adds a save/restore pair."
  [target state values]
  (let [assigned (:assigned state)
        remaining (apply dissoc assigned values)
        still-owned (set (vals remaining))
        released (vec (remove still-owned (map assigned (ordered-vregs values))))
        scratch? (set (get physical-registers target))
        state (expire-assigned state values)]
    (-> state
        (update :free (fn [free]
                        (into (vec (remove (set released) free))
                              (filter scratch? released))))
        (update :reserve #(into (vec (remove scratch? released)) %)))))

(defn- drop-backed-assignments
  "A reload in one arm does not satisfy a use in another. Values that already
  have a slot are dropped from the assignment at every label so the next use
  in this block loads them again. Values that were never spilled stay: their
  definition dominates the split. Callers skip this when nothing assigned is
  backed -- rebuilding the pool lists on a leaf scramble coalescing."
  [target pool assigned backed]
  (let [kept (into {} (remove (fn [[value _]] (contains? backed value)) assigned))
        lists (rebuild-pool-lists target pool kept)]
    {:assigned kept :free (:free lists) :reserve (:reserve lists)}))

(defn- physicalize-call
  [target instruction call-registers return-register]
  (let [op (:mir/op instruction)]
    (cond-> {:mir/op op :mir/arguments call-registers}
      (not= :mir/tail-call op) (assoc :mir/dst return-register)
      (contains? #{:mir/call :mir/tail-call} op)
      (assoc :mir/callee (:mir/callee instruction))
      (= :mir/runtime-call op)
      (assoc :mir/runtime (:mir/runtime instruction)
             :mir/context-offset (:mir/context-offset instruction))
      (= :mir/capability-call op)
      (assoc :mir/capability (:mir/capability instruction)
             :mir/kind (:mir/kind instruction)
             :mir/context-offset (:mir/context-offset instruction)))))

(defn- entry-argument-plan
  "Materialize a function's ABI inputs as canonical self-markers followed by a
  bounded set of direct entry spills and a parallel copy into allocator
  registers. Values in PRESERVED-VALUES take the callee-saved tier first so an
  entry argument that crosses a call is not immediately stored and reloaded.
  Unused inputs need only their marker. Inputs beyond the allocator profile are
  backed directly from their ABI registers and loaded lazily."
  [target pool instructions last-use slot-base stable-slots preserved-values]
  (let [[arguments remaining] (split-with #(= :mir/argument (:mir/op %))
                                          instructions)]
    (when (some #(= :mir/argument (:mir/op %)) remaining)
      (reject! :spill-required {:problem :non-prefix-argument}))
    (let [arguments (vec arguments)
          remaining (vec remaining)
          allocator-registers pool
          abi-registers (get call-argument-registers target)
          used (filterv #(contains? last-use (:mir/dst %)) arguments)]
      (let [scratch-count (count (get physical-registers target))
            initial {:scratch (vec (take scratch-count allocator-registers))
                     :preserved (vec (drop scratch-count allocator-registers))
                     :register-inputs [] :spill-inputs [] :assigned {}}
            {:keys [register-inputs spill-inputs assigned] :as placement}
            (reduce
             (fn [state instruction]
               (let [value (:mir/dst instruction)
                     primary (if (contains? preserved-values value)
                               :preserved :scratch)
                     secondary (if (= primary :preserved) :scratch :preserved)
                     tier (cond
                            (seq (get state primary)) primary
                            (seq (get state secondary)) secondary
                            :else nil)]
                 (if tier
                   (let [register (first (get state tier))]
                     (-> state
                         (update tier #(vec (rest %)))
                         (update :register-inputs conj [instruction register])
                         (assoc-in [:assigned value] register)))
                   (update state :spill-inputs conj instruction))))
             initial used)
            input-register (fn [instruction]
                             (or (get abi-registers (:mir/index instruction))
                                 (reject! :spill-required instruction)))
            [entry-spills next-slot]
            (reduce (fn [[slots next-slot] instruction]
                      (let [value (:mir/dst instruction)]
                        (if-let [slot (get stable-slots value)]
                          [(assoc slots value slot) next-slot]
                          [(assoc slots value next-slot) (inc next-slot)])))
                    [{} slot-base]
                    spill-inputs)
            markers (mapv #(assoc % :mir/dst (input-register %)) arguments)
            stores (mapv (fn [instruction]
                           {:mir/op :mir/spill-store
                            :mir/src (input-register instruction)
                            :mir/slot (get entry-spills (:mir/dst instruction))})
                         spill-inputs)
            copies (mapv (fn [[instruction register]]
                           {:mir/dst register
                            :mir/src (input-register instruction)})
                         register-inputs)
            scheduled (schedule-parallel-copies copies next-slot)]
        {:argument-count (count arguments)
         :remaining remaining
         :assigned assigned
         :entry-spills entry-spills
         :stable-slots (merge stable-slots entry-spills)
         :stable-slot-count next-slot
         :temp-slot next-slot
         :free (:scratch placement)
         :reserve (:preserved placement)
         :instructions (into markers (concat stores (:instructions scheduled)))
         :parameter-homes (when (and (empty? entry-spills)
                                     (= (count arguments) (count assigned)))
                            (mapv #(get assigned (:mir/dst %)) arguments))
         :used-temp? (:used-temp? scheduled)}))))

(defn- call-live-slots
  "Assign stable slots only to SSA values whose definition precedes a call and
  whose final use follows that call. Slots are ordered by definition, so the
  result is deterministic and independent of target register names."
  [instructions]
  (let [last-use (last-uses instructions)
        call-indexes (->> instructions
                          (keep-indexed (fn [index instruction]
                                          (when (call-operation? (:mir/op instruction))
                                            index)))
                          vec)
        definitions (->> instructions
                         (keep-indexed (fn [index instruction]
                                         (when (gmir/vreg? (:mir/dst instruction))
                                           [(:mir/dst instruction) index])))
                         vec)
        crossing (filter (fn [[value definition-index]]
                           (some (fn [call-index]
                                   (< definition-index call-index
                                      (get last-use value -1)))
                                 call-indexes))
                         definitions)]
    (into {} (map-indexed (fn [slot [value _]] [value slot]) crossing))))

(defn- straight-line-call-program? [instructions]
  (and (some #(call-operation? (:mir/op %)) instructions)
       (not-any? #(contains? #{:mir/label :mir/branch-zero :mir/branch-nonzero
                               :mir/jump :mir/phi}
                             (:mir/op %))
                 instructions)))

(defn- allocate-call-live
  "Allocate a straight-line call function while materializing only values live
  across a call. Register pressure outside calls deliberately falls back to the
  conservative all-vreg allocator rather than weakening correctness."
  [{:mir/keys [version target registers instructions] :as program}]
  (when-not (= :virtual registers)
    (reject! :registers-not-virtual program))
  (let [last-use (last-uses instructions)
        call-slots (call-live-slots instructions)
        allocator-registers (allocator-pool target {:leaf? false})
        return-register (get return-registers target)]
    (let [entry (entry-argument-plan target allocator-registers instructions
                                     last-use (count call-slots) call-slots #{})
          slots (:stable-slots entry)
          temp-slot (:temp-slot entry)]
      (when (> (+ (:stable-slot-count entry) 1) 4095)
        (reject! :spill-frame-too-large
                 {:frame-slots (:stable-slot-count entry)}))
      (letfn [(expire [state index just-defined]
                (let [expired (filter #(or (= index (get last-use %))
                                           (and (= just-defined %)
                                                (not (contains? last-use %))))
                                      (keys (:assigned state)))]
                  (expire-assigned-in-pool target state expired)))
            (ensure-source [state instruction value]
              (if (contains? (:assigned state) value)
                state
                (let [slot (get slots value)
                      register (first (:free state))]
                  (when-not (and (some? slot) register
                                 (contains? (:materialized state) value))
                    (reject! :spill-required instruction))
                  (-> state
                      (assoc-in [:assigned value] register)
                      (update :free #(vec (rest %)))
                      (update :out conj {:mir/op :mir/spill-load
                                         :mir/dst register :mir/slot slot})))))
            (ensure-sources [state instruction values]
              (reduce (fn [out value] (ensure-source out instruction value))
                      state (distinct values)))
            (allocate-dst [state instruction dst]
              (if-not (gmir/vreg? dst)
                state
                (let [register (first (:free state))]
                  (when-not register
                    (reject! :spill-required instruction))
                  (-> state
                      (assoc-in [:assigned dst] register)
                      (update :free #(vec (rest %)))))))]
      (let [result
            (reduce
             (fn [state [index {:mir/keys [op dst arguments] :as instruction}]]
               (if (call-operation? op)
                 (let [missing (remove #(or (contains? (:assigned state) %)
                                            (and (contains? slots %)
                                                 (contains? (:materialized state) %)))
                                       arguments)
                       _ (when (seq missing)
                           (reject! :spill-required instruction))
                       live-values (->> (keys (:assigned state))
                                        (filter #(> (get last-use % -1) index))
                                        ordered-vregs)
                       to-store (filter #(and (contains? slots %)
                                              (not (contains? (:materialized state) %)))
                                        live-values)
                       stores (mapv (fn [value]
                                      {:mir/op :mir/spill-store
                                       :mir/src (get-in state [:assigned value])
                                       :mir/slot (get slots value)})
                                    to-store)
                       call-registers (subvec (argument-registers-for-call target instruction)
                                              0 (count arguments))
                       copies (->> (map vector arguments call-registers)
                                   (keep (fn [[value register]]
                                           (when-let [source (get-in state
                                                                     [:assigned value])]
                                             {:mir/dst register :mir/src source})))
                                   vec)
                       scheduled (schedule-parallel-copies copies temp-slot)
                       loads (->> (map vector arguments call-registers)
                                  (keep (fn [[value register]]
                                          (when-not (contains? (:assigned state) value)
                                            {:mir/op :mir/spill-load
                                             :mir/dst register
                                             :mir/slot (get slots value)})))
                                  vec)
                       call (cond-> {:mir/op op :mir/arguments call-registers}
                              (not= :mir/tail-call op)
                              (assoc :mir/dst return-register)
                              (contains? #{:mir/call :mir/tail-call} op)
                              (assoc :mir/callee (:mir/callee instruction))
                              (= :mir/runtime-call op)
                              (assoc :mir/runtime (:mir/runtime instruction)
                                     :mir/context-offset
                                     (:mir/context-offset instruction))
                              (= :mir/capability-call op)
                              (assoc :mir/capability (:mir/capability instruction)
                                     :mir/kind (:mir/kind instruction)
                                     :mir/context-offset
                                     (:mir/context-offset instruction)))
                       state (-> state
                                 (update :out into stores)
                                 (update :out into (:instructions scheduled))
                                 (update :out into loads)
                                 (update :out conj call)
                                 (update :materialized into to-store)
                                 (update :used-temp? #(or % (:used-temp? scheduled)))
                                 (assoc :assigned (if (gmir/vreg? dst)
                                                    {dst return-register} {}))
                                 (assoc :free (vec (remove #{return-register}
                                                          allocator-registers))))]
                   (expire state index dst))
                 (let [source-values (filter gmir/vreg? (sources instruction))
                       state (ensure-sources state instruction source-values)
                       state (allocate-dst state instruction dst)
                       allocated (reduce-kv
                                  (fn [out key value]
                                    (assoc out key
                                    (cond
                                      (gmir/vreg? value)
                                      (get-in state [:assigned value])
                                      (and (= key :mir/arguments) (vector? value))
                                      (mapv #(get-in state [:assigned %]) value)
                                      :else value)))
                                  {} instruction)
                       state (update state :out conj allocated)]
                   (expire state index dst))))
             {:assigned (:assigned entry) :free (:free entry)
              :reserve (:reserve entry)
              :materialized (set (keys (:entry-spills entry)))
              :used-temp? (:used-temp? entry) :out (:instructions entry)}
             (map-indexed (fn [offset instruction]
                            [(+ (:argument-count entry) offset) instruction])
                          (:remaining entry)))
            frame-slots (+ (:stable-slot-count entry)
                           (if (:used-temp? result) 1 0))]
        (validate-flat!
         {:mir/version version
          :mir/target target
          :mir/registers :physical
          :mir/frame-slots frame-slots
          :mir/instructions (:out result)}))))))

(defn- store-at-definition
  "Splice the spill-store in immediately after VALUE was defined, rather than
  leaving it where the register ran out.

  This allocator walks one flat instruction list that contains labels and
  branches, so the point of exhaustion can sit inside one arm of a branch while
  the reload lands in the other. A store left there writes a slot on a path that
  was not taken, and the other path reads whatever was in it. A definition
  dominates every use of its value, because the program is in SSA form, so a
  store placed there is executed before any reload of it can be reached.

  Every definition position at or after the splice moves along by one."
  [{:keys [out def-position] :as state} value register slot]
  (let [position (or (get def-position value)
                     (reject! :spill-required
                              {:problem :no-definition-to-store-at :value value}))
        store {:mir/op :mir/spill-store :mir/src register :mir/slot slot}]
    (assoc state
           :out (into (conj (subvec out 0 position) store) (subvec out position))
           :def-position (reduce-kv (fn [positions other other-position]
                                      (assoc positions other
                                             (if (>= other-position position)
                                               (inc other-position)
                                               other-position)))
                                    {} def-position))))

(defn- allocate-without-spills
  "Linear-scan allocation. The pool grows on demand; when it is empty the
  live value with the furthest next use is stored, not every SSA value.
  A body that fits never reaches the spill step, so its assignment is
  byte-for-byte what it was.

  A function that contains a call is offered the non-leaf pool (scratch then
  preserved, no leaf-tier caller-saved). Values live across a call prefer the
  preserved tier at their definition so a call does not have to move them.
  Remaining live caller-saved values are stored at their definition -- the
  store dominates every reload, including the arm that does not contain the
  call -- then dropped from the assignment. A reload in one arm does not
  satisfy a use in another: at every label after the entry, backed values
  that are currently assigned leave the assignment so the next use in that
  block loads them again. The call itself uses the ABI registers. Pressure
  that still cannot complete falls out as :spill-required."
  [{:mir/keys [version target registers instructions] :as program} merge-slots
   current-function]
  (when-not (= :virtual registers)
    (reject! :registers-not-virtual program))
  (let [last-use (last-uses instructions)
        indexes (use-indexes instructions)
        calls? (boolean (some #(call-operation? (:mir/op %)) instructions))
        pool (allocator-pool target {:leaf? (not calls?)})
        crossing (if calls? (set (keys (call-live-slots instructions))) #{})
        preserved-set (set (get preserved-registers target))
        return-register (get return-registers target)
        ;; AArch64's preserved entry assignment is safe across its closed guest
        ;; call ABI.  Keep x86-64 on the established scratch-first plan: native
        ;; host-callback and self-tail helpers rely on that physical placement.
        entry (entry-argument-plan target pool instructions last-use
                                   merge-slots {}
                                   (if (= :aarch64 target) crossing #{}))
        parameter-homes (:parameter-homes entry)
        direct-reentry? (and (= :aarch64 target)
                             current-function
                             parameter-homes
                             (some #(and (= :mir/tail-call (:mir/op %))
                                         (= current-function (:mir/callee %)))
                                   instructions))
        recur-home-candidates
        (if direct-reentry?
          (direct-recur-home-candidates instructions current-function
                                        parameter-homes indexes)
          {})]
    (letfn [(spill-assigned [state value instruction]
              (let [register (get-in state [:assigned value])]
                (when-not register
                  (reject! :spill-required instruction))
                (let [existing (get-in state [:backed value])
                      slot (or existing (:next-slot state))
                      next-slot (if existing
                                  (:next-slot state)
                                  (inc (:next-slot state)))]
                  (when (> next-slot 4095)
                    (reject! :spill-frame-too-large {:frame-slots next-slot}))
                  ;; A value already in a slot needs no second store: it never
                  ;; changes, so what was written the first time is still what
                  ;; is there.
                  (cond-> (-> state
                              (assoc-in [:backed value] slot)
                              (assoc :next-slot next-slot)
                              (update :assigned dissoc value)
                              (update :free conj register))
                    (not existing) (store-at-definition value register slot)))))
            (take-register [state instruction protected prefer]
              (let [primary (if (= prefer :preserved) :reserve :free)
                    secondary (if (= prefer :preserved) :free :reserve)
                    from-primary (first (get state primary))]
                (if from-primary
                  [(assoc state primary (vec (rest (get state primary))))
                   from-primary]
                  (let [from-secondary (first (get state secondary))]
                    (if from-secondary
                      [(assoc state secondary (vec (rest (get state secondary))))
                       from-secondary]
                      ;; No second pass with an empty PROTECTED set. Evicting
                      ;; an operand of the instruction being allocated loses it:
                      ;; the source was just loaded and nothing reloads it, and
                      ;; the destination does not exist yet. Rejecting here
                      ;; sends the function to the conservative all-vreg path,
                      ;; which is slower and correct. Unreachable in both
                      ;; suites today -- an instruction would need every
                      ;; register held by its own operands.
                      (if-let [victim (furthest-victim (:assigned state)
                                                       indexes
                                                       (:index state)
                                                       protected)]
                        (let [register (get-in state [:assigned victim])
                              state (spill-assigned state victim instruction)]
                          [(assoc state :free (vec (rest (:free state))))
                           register])
                        (reject! :spill-required instruction)))))))
            (emit-call [state index instruction]
              (let [{:mir/keys [op dst arguments callee]} instruction
                    direct-recur? (and direct-reentry?
                                       (= :mir/tail-call op)
                                       (= current-function callee)
                                       ;; A backed source needs a load. Mixing
                                       ;; those loads with a parallel register
                                       ;; copy can overwrite a still-needed
                                       ;; source, so that site retains the
                                       ;; ordinary ABI tail path.
                                       (every? #(contains? (:assigned state) %)
                                               arguments))]
                (if direct-recur?
                  (let [copies (mapv (fn [value register]
                                       {:mir/dst register
                                        :mir/src (get-in state [:assigned value])})
                                     arguments parameter-homes)
                        temp-slot (or (:temp-slot state) (:next-slot state))
                        scheduled (schedule-parallel-copies copies temp-slot)
                        pinning-temp? (and (:used-temp? scheduled)
                                           (not (:used-temp? state)))]
                    (-> state
                        (update :out into (:instructions scheduled))
                        (update :out conj {:mir/op :mir/recur
                                           :mir/arguments parameter-homes})
                        (assoc :used-temp? (or (:used-temp? state)
                                               (:used-temp? scheduled))
                               :next-slot (cond-> (:next-slot state)
                                            pinning-temp? inc)
                               :temp-slot (if (:used-temp? scheduled)
                                            temp-slot
                                            (:temp-slot state)))))
                  (let [call-registers (subvec (argument-registers-for-call
                                            target instruction)
                                           0 (count arguments))
                    live-across (->> (keys (:assigned state))
                                     (filter #(> (get last-use % -1) index))
                                     ordered-vregs)
                    state (reduce (fn [state value]
                                    (let [register (get-in state [:assigned value])]
                                      (if (contains? preserved-set register)
                                        state
                                        (spill-assigned state value instruction))))
                                  state live-across)
                    copies (->> (map vector arguments call-registers)
                                (keep (fn [[value register]]
                                        (when-let [source (get-in state
                                                                  [:assigned value])]
                                          {:mir/dst register :mir/src source})))
                                vec)
                    loads (->> (map vector arguments call-registers)
                               (keep (fn [[value register]]
                                       (when-not (contains? (:assigned state) value)
                                         (let [slot (get (:backed state) value)]
                                           (when-not slot
                                             (reject! :spill-required instruction))
                                           {:mir/op :mir/spill-load
                                            :mir/dst register
                                            :mir/slot slot}))))
                               vec)
                    temp-slot (or (:temp-slot state) (:next-slot state))
                    scheduled (schedule-parallel-copies copies temp-slot)
                    pinning-temp? (and (:used-temp? scheduled)
                                       (not (:used-temp? state)))
                    state (-> state
                              (update :out into (:instructions scheduled))
                              (update :out into loads)
                              (update :out conj
                                      (physicalize-call target instruction
                                                        call-registers
                                                        return-register))
                              (assoc :used-temp? (or (:used-temp? state)
                                                     (:used-temp? scheduled))
                                     :next-slot (cond-> (:next-slot state)
                                                  pinning-temp? inc)
                                     :temp-slot (if (:used-temp? scheduled)
                                                  temp-slot
                                                  (:temp-slot state))))
                    kept (into {}
                               (filter (fn [[_ register]]
                                         (contains? preserved-set register))
                                       (:assigned state)))
                    kept (if (and (gmir/vreg? dst) (not= :mir/tail-call op))
                           (assoc kept dst return-register)
                           kept)
                    lists (rebuild-pool-lists target pool kept)
                    state (assoc state
                                 :assigned kept
                                 :free (:free lists)
                                 :reserve (:reserve lists))
                    state (if (and (gmir/vreg? dst)
                                   (contains? crossing dst)
                                   (seq (:reserve state)))
                            (let [preserved (first (:reserve state))]
                              (-> state
                                  (update :out conj {:mir/op :mir/move
                                                     :mir/dst preserved
                                                     :mir/src return-register})
                                  (assoc-in [:assigned dst] preserved)
                                  (assoc :reserve (vec (rest (:reserve state))))
                                  (update :free conj return-register)))
                            state)
                    expired (filter #(= index (get last-use %))
                                    (keys (:assigned state)))
                    state (expire-assigned-in-pool target state expired)]
                (if (gmir/vreg? dst)
                  (assoc-in state [:def-position dst] (count (:out state)))
                  state)))))]
      (loop [index (:argument-count entry), remaining (:remaining entry)
             assigned (:assigned entry), free (:free entry)
             reserve (:reserve entry)
             backed (:entry-spills entry)
             next-slot (cond-> (:stable-slot-count entry)
                         (:used-temp? entry) inc)
             out (cond-> (:instructions entry)
                   direct-reentry? (conj {:mir/op :mir/reentry
                                          :mir/parameters parameter-homes}))
             used-temp? (:used-temp? entry)
             temp-slot (:temp-slot entry)
             ;; Everything the entry plan assigned is in place by the end of its
             ;; own instructions, so that is where a store of one of them goes.
             def-position (zipmap (keys (:assigned entry))
                                  (repeat (count (:instructions entry))))]
        (if-let [instruction (first remaining)]
          (if (call-operation? (:mir/op instruction))
            (let [state (emit-call {:assigned assigned :free free :reserve reserve
                                    :backed backed :next-slot next-slot
                                    :out out :used-temp? used-temp?
                                    :temp-slot temp-slot
                                    :def-position def-position
                                    :index index}
                                   index instruction)]
              (recur (inc index) (next remaining)
                     (:assigned state) (vec (:free state)) (:reserve state)
                     (:backed state) (:next-slot state)
                     (:out state) (:used-temp? state) (:temp-slot state)
                     (:def-position state)))
            (let [drop? (and (= :mir/label (:mir/op instruction))
                             (pos? index)
                             (some #(contains? backed %) (keys assigned)))
                  block (if drop?
                          (drop-backed-assignments target pool assigned backed)
                          {:assigned assigned :free free :reserve reserve})
                  assigned (:assigned block)
                  free (:free block)
                  reserve (:reserve block)
                  srcs (distinct (filter gmir/vreg? (sources instruction)))
                  protected (set srcs)
                  loaded (reduce (fn [state source]
                                   (if (contains? (:assigned state) source)
                                     state
                                     (let [slot (get (:backed state) source)]
                                       (when-not slot
                                         (reject! :spill-required instruction))
                                       (let [prefer (if (contains? crossing source)
                                                      :preserved :scratch)
                                             [state register]
                                             (take-register (assoc state :index index)
                                                            instruction
                                                            protected
                                                            prefer)]
                                         (-> state
                                             (assoc-in [:assigned source] register)
                                             (update :out conj {:mir/op :mir/spill-load
                                                                :mir/dst register
                                                                :mir/slot slot}))))))
                                 {:assigned assigned :free free :reserve reserve
                                  :backed backed :next-slot next-slot
                                  :out out :index index
                                  :def-position def-position}
                                 srcs)
                  assigned (:assigned loaded)
                  free (:free loaded)
                  reserve (:reserve loaded)
                  backed (:backed loaded)
                  next-slot (:next-slot loaded)
                  out (:out loaded)
                  def-position (:def-position loaded)]
              (let [dst (:mir/dst instruction)
                    prefer (if (contains? crossing dst) :preserved :scratch)
                    [assigned free reserve backed next-slot out def-position]
                    (if (gmir/vreg? dst)
                      (do
                        (when (contains? assigned dst)
                          (reject! :multiple-definition instruction))
                        (let [desired-home (get recur-home-candidates dst)
                              recur-use (first (get indexes dst))
                              home-owner (when desired-home
                                           (some (fn [[value register]]
                                                   (when (= desired-home register)
                                                     value))
                                                 assigned))
                              ;; A definition may overwrite its requested home
                              ;; only when the register is free, or when the old
                              ;; value is an operand whose final CFG use is this
                              ;; very instruction.  Physical integer operations
                              ;; read all operands before writing DST, so this
                              ;; preserves simultaneous SSA semantics.  Any
                              ;; interference falls back to ordinary allocation
                              ;; and the proven parallel-copy scheduler.
                              direct-home (when (and desired-home
                                                     (contains?
                                                      schedulable-integer-operations
                                                      (:mir/op instruction))
                                                     (straight-line-to-recur?
                                                      instructions index recur-use)
                                                     (or (nil? home-owner)
                                                         (and (contains? protected
                                                                         home-owner)
                                                              (= index
                                                                 (get last-use
                                                                      home-owner)))))
                                            desired-home)
                              dying-left (when (and (= prefer :scratch)
                                                    (gmir/vreg? (:mir/left instruction))
                                                    (= index (get last-use
                                                                  (:mir/left instruction))))
                                           (get assigned (:mir/left instruction)))
                              from-primary (if (= prefer :preserved)
                                             (first reserve)
                                             (first free))
                              register (or direct-home from-primary dying-left)
                              [state register]
                              (if register
                                [{:assigned assigned
                                  :free (if direct-home
                                          (vec (remove #{direct-home} free))
                                          (if (and from-primary (= prefer :scratch))
                                            (vec (rest free))
                                            free))
                                  :reserve (if direct-home
                                             (vec (remove #{direct-home} reserve))
                                             (if (and from-primary
                                                      (= prefer :preserved))
                                               (vec (rest reserve))
                                               reserve))
                                  :backed backed
                                  :next-slot next-slot :out out :index index
                                  :def-position def-position}
                                 register]
                                (take-register {:assigned assigned :free free
                                                :reserve reserve :backed backed
                                                :def-position def-position
                                                :next-slot next-slot :out out
                                                :index index}
                                               instruction
                                               protected
                                               prefer))]
                          [(assoc (:assigned state) dst register)
                           (:free state) (:reserve state)
                           (:backed state) (:next-slot state) (:out state)
                           (:def-position state)]))
                      [assigned free reserve backed next-slot out def-position])
                    allocated (reduce-kv
                               (fn [result key value]
                                 (assoc result key
                                        (cond
                                          (gmir/vreg? value) (get assigned value)
                                          (and (= key :mir/arguments) (vector? value))
                                          (mapv assigned value)
                                          :else value)))
                               {} instruction)
                    allocated (case (:mir/op allocated)
                                :mir/merge-store
                                {:mir/op :mir/spill-store
                                 :mir/src (:mir/src allocated)
                                 :mir/slot (:mir/slot allocated)}
                                :mir/merge-load
                                {:mir/op :mir/spill-load
                                 :mir/dst (:mir/dst allocated)
                                 :mir/slot (:mir/slot allocated)}
                                allocated)
                    expired (filter #(or (= index (get last-use %))
                                         (and (= dst %)
                                              (not (contains? last-use %))))
                                    (keys assigned))
                    state (if calls?
                            (expire-assigned-in-pool
                             target
                             {:assigned assigned :free free :reserve reserve}
                             expired)
                            (expire-assigned
                             {:assigned assigned :free free}
                             expired))]
                (recur (inc index) (next remaining)
                       (:assigned state) (vec (:free state))
                       (if calls? (:reserve state) reserve)
                       backed next-slot
                       (conj out allocated) used-temp? temp-slot
                       (if (gmir/vreg? dst)
                         (assoc def-position dst (inc (count out)))
                         def-position)))))
          (let [out (if (some #(= :mir/recur (:mir/op %)) out)
                      out
                      (vec (remove #(= :mir/reentry (:mir/op %)) out)))]
            (validate-flat!
             {:mir/version version
              :mir/target target
              :mir/registers :physical
              :mir/frame-slots (+ next-slot
                                  (if used-temp? 1 0))
              :mir/instructions out})))))))

(defn- validate-ssa-definition-order [instructions]
  (:ordered
   (reduce (fn [{:keys [defined ordered] :as state}
                {:mir/keys [dst] :as instruction}]
             (doseq [source (filter gmir/vreg? (sources instruction))]
               (when-not (contains? defined source)
                 (reject! :use-before-definition instruction)))
             (if (gmir/vreg? dst)
               (do
                 (when (contains? defined dst)
                   (reject! :multiple-definition instruction))
                 {:defined (conj defined dst) :ordered (conj ordered dst)})
               state))
           {:defined #{} :ordered []}
           instructions)))

(defn- slot-sources
  "Values whose frame contents are read by INSTRUCTION. A lowered merge-load
  is a slot use: the value was written on each incoming edge, not defined at
  the join."
  [instruction]
  (if (= :mir/merge-load (:mir/op instruction))
    [(:mir/dst instruction)]
    (filter gmir/vreg? (sources instruction))))

(defn- slot-definition
  "The frame value defined by INSTRUCTION. A merge-store defines the phi
  destination on its edge; the later merge-load only materializes that slot."
  [instruction merge-dst-by-slot]
  (case (:mir/op instruction)
    :mir/merge-store (get merge-dst-by-slot (:mir/slot instruction))
    :mir/merge-load nil
    (instruction-def instruction)))

(defn- slot-block-use-def [instructions blocks merge-dst-by-slot]
  (mapv (fn [{:keys [start end]}]
          (reduce (fn [{:keys [uses defs]} index]
                    (let [instruction (nth instructions index)
                          read (remove defs (slot-sources instruction))
                          definition (slot-definition instruction merge-dst-by-slot)]
                      {:uses (into uses read)
                       :defs (cond-> defs (gmir/vreg? definition)
                               (conj definition))}))
                  {:uses #{} :defs #{}}
                  (range start (inc end))))
        blocks))

(defn- slot-liveness [instructions merge-dst-by-slot]
  (let [blocks (basic-blocks instructions)
        label->block (label-block-indexes instructions blocks)
        successors (block-successors instructions blocks label->block)
        use-def (slot-block-use-def instructions blocks merge-dst-by-slot)
        block-count (count blocks)
        empty (vec (repeat block-count #{}))]
    (loop [live-in empty live-out empty]
      (let [next-out (mapv (fn [block-index]
                             (reduce into #{}
                                     (map #(nth live-in %)
                                          (nth successors block-index))))
                           (range block-count))
            next-in (mapv (fn [block-index]
                            (let [{:keys [uses defs]} (nth use-def block-index)]
                              (into uses (remove defs (nth next-out block-index)))))
                          (range block-count))]
        (if (and (= next-in live-in) (= next-out live-out))
          {:blocks blocks :live-in next-in :live-out next-out}
          (recur next-in next-out))))))

(defn- add-interference [graph definition live]
  (if-not (gmir/vreg? definition)
    graph
    (reduce (fn [out value]
              (if (= definition value)
                out
                (-> out
                    (update definition (fnil conj #{}) value)
                    (update value (fnil conj #{}) definition))))
            (update graph definition (fnil identity #{}))
            live)))

(defn- spill-interference
  "Build conservative SSA frame-slot interference from fixed-point CFG
  liveness. Mutually exclusive branch values may share a slot; values live
  together at a join or around a back edge may not."
  [instructions merge-dst-by-slot]
  (let [{:keys [blocks live-out]} (slot-liveness instructions merge-dst-by-slot)]
    (reduce
     (fn [graph block-index]
       (let [{:keys [start end]} (nth blocks block-index)]
         (:graph
          (reduce
           (fn [{:keys [graph live]} index]
             (let [instruction (nth instructions index)
                   definition (slot-definition instruction merge-dst-by-slot)
                   graph (add-interference graph definition live)
                   live (into (cond-> live (gmir/vreg? definition)
                               (disj definition))
                              (slot-sources instruction))]
               {:graph graph :live live}))
           {:graph graph :live (nth live-out block-index)}
           (range end (dec start) -1)))))
     {}
     (range (count blocks)))))

(defn- spill-slots [instructions offset merge-dst-by-slot]
  (let [ordered (validate-ssa-definition-order instructions)
        interference (spill-interference instructions merge-dst-by-slot)]
    (reduce (fn [slots value]
              (let [unavailable (into #{} (keep slots)
                                      (get interference value))
                    slot (first (remove unavailable (range offset 4096)))]
                (when-not slot
                  (reject! :spill-frame-too-large {:frame-slots 4096}))
                (assoc slots value slot)))
            {}
            ordered)))

(defn- allocate-with-spills
  [{:mir/keys [version target instructions] :as program} merge-dst-by-slot]
  (let [slots (spill-slots instructions 0 merge-dst-by-slot)
        slot-count (if (seq slots) (inc (apply max (vals slots))) 0)
        [r0 r1 r2 r3] (get physical-registers target)
        argument-registers (get call-argument-registers target)]
    (when (> slot-count 4095)
      (reject! :spill-frame-too-large {:frame-slots slot-count}))
    (letfn [(slot-of [instruction value]
              (or (get slots value)
                  (reject! :use-before-definition instruction)))
            (load-value [instruction value register]
              {:mir/op :mir/spill-load :mir/dst register
               :mir/slot (slot-of instruction value)})
            (store-value [instruction value register]
              {:mir/op :mir/spill-store :mir/src register
               :mir/slot (slot-of instruction value)})]
      (validate-flat!
        {:mir/version version
        :mir/target target
        :mir/registers :physical
        :mir/frame-slots slot-count
        :mir/instructions
        (vec
         (mapcat
          (fn [{:mir/keys [op dst input left right test value callee arguments
                           base length index stored offset size maximum]
                :as instruction}]
            (case op
              :mir/argument
              (let [register (or (get argument-registers (:mir/index instruction))
                                 (reject! :argument-index-invalid instruction))]
                [(assoc instruction :mir/dst register)
                 (store-value instruction dst register)])

              :mir/constant
              [(assoc instruction :mir/dst r0)
               (store-value instruction dst r0)]

              :mir/data-address
              [(assoc instruction :mir/dst r0)
               (store-value instruction dst r0)]

              :mir/merge-store
              (let [phi-dst (or (get merge-dst-by-slot (:mir/slot instruction))
                                (reject! :unknown-merge-slot instruction))]
                [(load-value instruction (:mir/src instruction) r0)
                 (store-value instruction phi-dst r0)])

              :mir/merge-load
              []

              :mir/quotient-constant
              [(load-value instruction left r0)
               {:mir/op op :mir/dst r0 :mir/left r0
                :mir/divisor (:mir/divisor instruction)}
               (store-value instruction dst r0)]

              (:mir/add :mir/subtract :mir/multiply :mir/quotient
               :mir/bit-and :mir/bit-or :mir/bit-xor
               :mir/shift-left :mir/shift-right-signed :mir/shift-right-unsigned
               :mir/f64-add :mir/f64-subtract :mir/f64-multiply
               :mir/f64-divide :mir/f64-min :mir/f64-max
               :mir/f64-equal :mir/f64-less-than :mir/f64-less-or-equal
               :mir/f64-greater-than :mir/f64-greater-or-equal
               :mir/f64-unordered
               :mir/equal :mir/less-than :mir/greater-than
               :mir/less-or-equal :mir/greater-or-equal)
              [(load-value instruction left r0)
               (load-value instruction right r1)
               {:mir/op op :mir/dst r0 :mir/left r0 :mir/right r1}
               (store-value instruction dst r0)]

              :mir/f64-sqrt
              [(load-value instruction input r0)
               {:mir/op op :mir/dst r0 :mir/input r0}
               (store-value instruction dst r0)]

              (:mir/kernel-load-u8 :mir/kernel-load-u32
               :mir/kernel-try-lock-u32 :mir/kernel-unlock-u32)
              [(load-value instruction base r0)
               (load-value instruction length r1)
               (load-value instruction index r2)
               {:mir/op op :mir/dst r0 :mir/base r0 :mir/length r1
                :mir/index r2 :mir/maximum maximum}
               (store-value instruction dst r0)]

              (:mir/kernel-store-u8 :mir/kernel-store-u32)
              [(load-value instruction base r0)
               (load-value instruction length r1)
               (load-value instruction index r2)
               (load-value instruction stored r3)
               {:mir/op op :mir/dst r3 :mir/base r0 :mir/length r1
                :mir/index r2 :mir/stored r3 :mir/maximum maximum}
               (store-value instruction dst r3)]

              :mir/kernel-subregion
              [(load-value instruction base r0)
               (load-value instruction length r1)
               (load-value instruction offset r2)
               (load-value instruction size r3)
               {:mir/op op :mir/dst r0 :mir/base r0 :mir/length r1
                :mir/offset r2 :mir/size r3}
               (store-value instruction dst r0)]

              :mir/x86-privileged
              (let [argument-registers (subvec [r0 r1] 0 (count arguments))]
                (concat
                 (mapv (fn [value register]
                         (load-value instruction value register))
                       arguments argument-registers)
                 [{:mir/op op :mir/dst r0 :mir/action (:mir/action instruction)
                   :mir/arguments argument-registers}
                  (store-value instruction dst r0)]))

              (:mir/branch-zero :mir/branch-nonzero)
              [(load-value instruction test r0)
               (assoc instruction :mir/test r0)]

              :mir/tail-call
              (let [call-registers (subvec (get call-argument-registers target)
                                           0 (count arguments))]
                (concat
                 (mapv (fn [argument register]
                         (load-value instruction argument register))
                       arguments call-registers)
                 [{:mir/op :mir/tail-call :mir/callee callee
                   :mir/arguments call-registers}]))

              (:mir/call :mir/runtime-call :mir/capability-call)
              (let [call-registers (subvec (argument-registers-for-call target instruction)
                                           0 (count arguments))]
                (concat
                 (mapv (fn [value register]
                         (load-value instruction value register))
                       arguments call-registers)
                 [(cond-> {:mir/op op
                           :mir/dst (get return-registers target)
                           :mir/arguments call-registers}
                    (= :mir/call op) (assoc :mir/callee callee)
                    (= :mir/runtime-call op)
                    (assoc :mir/runtime (:mir/runtime instruction)
                           :mir/context-offset (:mir/context-offset instruction))
                    (= :mir/capability-call op)
                    (assoc :mir/capability (:mir/capability instruction)
                           :mir/kind (:mir/kind instruction)
                           :mir/context-offset (:mir/context-offset instruction)))
                  (store-value instruction dst (get return-registers target))]))

              :mir/return
              [(load-value instruction value r0)
               (assoc instruction :mir/value r0)]

              (:mir/label :mir/jump) [instruction]
              (reject! :unsupported-spill-operation instruction)))
          instructions))}))))

(defn- back-edge?
  "Does any jump or branch in INSTRUCTIONS target a label at or before it?

  ADR 0012 routes functions with control flow to the linear scanner,
  including those with a back edge. This predicate is not a routing guard.
  Leftover pressure still falls back to all-vreg via `:spill-required`."
  [instructions]
  (let [label-index (reduce-kv (fn [indexes index instruction]
                                 (if (= :mir/label (:mir/op instruction))
                                   (assoc indexes (:mir/id instruction) index)
                                   indexes))
                               {} instructions)]
    (boolean
     (some (fn [[index instruction]]
             (and (contains? #{:mir/jump :mir/branch-zero
                               :mir/branch-nonzero} (:mir/op instruction))
                  (when-let [target (get label-index (:mir/target instruction))]
                    (<= target index))))
           (map-indexed vector instructions)))))

(defn- allocate-with-policy
  "Try the linear scanner, including call-clobber handling. A function that
  still cannot complete falls back to the conservative all-vreg path. Returns
  [allocated-program frame-policy].

  Call plus a backward jump uses the scanner (`:call-live`) when it
  completes. After `lower-phis`, latch last-uses sit after their defs, so a
  prefix-argument terminating call+loop is not `:spill-required`. Iteration
  23's empty set was `:non-prefix-argument` (label before `:mir/argument`).
  Iteration 27: the full amu suite with `back-edge?` false failed only the
  production all-vreg policy asserts. `last-uses` is CFG-backed."
  [program]
  (let [current-function (::current-function (meta program))]
    (validate-flat! program)
    (let [{:keys [program merge-slots merge-dst-by-slot]} (lower-phis program)
        calls? (boolean (some #(call-operation? (:mir/op %))
                              (:mir/instructions program)))]
      (let [schedule-allocated
            (fn [allocated]
              (schedule-program allocated))]
        (try
          (let [allocated (schedule-allocated
                           (coalesce-phi-transports
                            (allocate-without-spills program merge-slots
                                                     current-function)
                            merge-slots))]
            [allocated (if calls? :call-live :allocator)])
          (catch #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) error
            (if (= :spill-required (:problem (ex-data error)))
              [(schedule-allocated
                (allocate-with-spills program merge-dst-by-slot))
               (if calls? :all-vregs :allocator)]
              (throw error))))))))

(defn- allocate-flat
  "Allocate virtual MIR deterministically. No-call bodies spill only values
  that do not fit. Call-containing bodies use the same scanner, keeping
  live-across values in the preserved tier; leftover pressure still takes
  the conservative all-vreg path."
  [program]
  (first (allocate-with-policy program)))

(defn allocate-registers
  "Allocate a legacy flat program or every function in a v3 module. A function
  containing a straight-line call stores only values live across that call and
  reloads them lazily. A function that also has control flow uses the linear
  scanner: live-across values prefer preserved registers, and remaining
  caller-saved values are stored at their definition. Entry arguments beyond
  the four-register allocator profile use bounded direct ABI spills. Leftover
  pressure that the linear allocator cannot complete still takes the
  conservative all-vreg path. Pure integer scheduling runs after allocation on
  physical MIR, one basic block at a time."
  [{:mir/keys [version target registers entry functions] :as program}]
  (validate! program)
  (if (= 3 version)
    (do
      (when-not (= :virtual registers)
        (reject! :registers-not-virtual program))
      (validate!
       {:mir/version 3
        :mir/target target
        :mir/registers :physical
        :mir/entry entry
        :mir/functions
        (mapv (fn [{:mir/keys [name arity instructions]}]
                (let [virtual {:mir/version 3 :mir/target target
                               :mir/registers :virtual
                               :mir/instructions instructions}
                      [allocated frame-policy]
                      (if (straight-line-call-program? instructions)
                        (try
                          [(schedule-program (allocate-call-live virtual))
                           :call-live]
                          (catch #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) error
                            (if (= :spill-required (:problem (ex-data error)))
                              (allocate-with-policy
                               (vary-meta virtual assoc ::current-function name))
                              (throw error))))
                        (allocate-with-policy
                         (vary-meta virtual assoc ::current-function name)))]
                  {:mir/name name
                   :mir/arity arity
                   :mir/frame-slots (:mir/frame-slots allocated)
                   :mir/frame-policy frame-policy
                   :mir/instructions (:mir/instructions allocated)}))
              functions)}))
    (allocate-flat program)))
