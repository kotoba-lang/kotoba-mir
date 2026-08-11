(ns kotoba.mir
  "Closed target-selected Machine IR and deterministic allocation."
  (:require [kotoba.gmir :as gmir]))

(def version 3)
(def supported-versions #{1 2 3})
(def targets #{:x86-64 :aarch64})

(def physical-registers
  {:x86-64 [:x86-64/rax :x86-64/rcx :x86-64/rdx :x86-64/r8]
   :aarch64 [:aarch64/x0 :aarch64/x1 :aarch64/x2 :aarch64/x3]})

(def call-argument-registers
  {:x86-64 [:x86-64/rdi :x86-64/rsi :x86-64/rdx :x86-64/rcx :x86-64/r8]
   :aarch64 [:aarch64/x0 :aarch64/x1 :aarch64/x2 :aarch64/x3 :aarch64/x4]})

(def return-registers
  {:x86-64 :x86-64/rax
   :aarch64 :aarch64/x0})

(defn- reject! [problem instruction]
  (throw (ex-info (str "MIR rejected: " (name problem))
                  {:phase :mir :problem problem :instruction instruction})))

(def instruction-keysets
  {:mir/argument #{:mir/op :mir/dst :mir/index}
   :mir/constant #{:mir/op :mir/dst :mir/value}
   :mir/add #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/subtract #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/multiply #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/quotient #{:mir/op :mir/dst :mir/left :mir/right}
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
   :mir/equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/less-than #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/greater-than #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/less-or-equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/greater-or-equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/spill-load #{:mir/op :mir/dst :mir/slot}
   :mir/spill-store #{:mir/op :mir/src :mir/slot}
   :mir/move #{:mir/op :mir/dst :mir/src}
   :mir/label #{:mir/op :mir/id}
   :mir/branch-zero #{:mir/op :mir/test :mir/target}
   :mir/jump #{:mir/op :mir/target}
   :mir/phi #{:mir/op :mir/dst :mir/incomings}
   :mir/call #{:mir/op :mir/dst :mir/callee :mir/arguments}
   :mir/return #{:mir/op :mir/value}})

(def ^:private v1-operations
  (disj (set (keys instruction-keysets)) :mir/phi :mir/call))

(def ^:private v2-operations
  (disj (set (keys instruction-keysets)) :mir/call))

(def ^:private v3-operations
  (set (keys instruction-keysets)))

(defn- operations-for [program-version]
  (case program-version
    1 v1-operations
    2 v2-operations
    3 v3-operations
    #{}))

(defn- physical-register? [target value]
  (contains? (set (concat (get physical-registers target)
                          (get call-argument-registers target)))
             value))

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
        (doseq [register (concat
                          (keep instruction [:mir/dst :mir/src :mir/input
                                             :mir/left :mir/right :mir/test])
                          (when (vector? (:mir/arguments instruction))
                            (:mir/arguments instruction)))]
          (when-not (register? register)
            (reject! :register-profile-violation instruction)))
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
        (when (= op :mir/call)
          (when-not (and (= 3 version)
                         (gmir/function-id? (:mir/callee instruction))
                         (vector? (:mir/arguments instruction))
                         (<= (count (:mir/arguments instruction)) 5))
            (reject! :invalid-call instruction))
          (when (= :physical registers)
            (when-not (and (= (:mir/dst instruction)
                              (get return-registers target))
                           (= (:mir/arguments instruction)
                              (subvec (get call-argument-registers target)
                                      0 (count (:mir/arguments instruction)))))
              (reject! :physical-call-profile-violation instruction))))
        (when (and (= op :mir/constant)
                   (not (gmir/i64-value? (:mir/value instruction))))
          (reject! :constant-not-i64 instruction))
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
        (when (contains? #{:mir/label :mir/branch-zero :mir/jump} op)
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
                              :mir/incomings :gmir/incomings)
                            (cond
                              (= key :mir/op) (keyword "gmir" (name value))
                              (= key :mir/incomings)
                              (mapv (fn [incoming]
                                      {:gmir/predecessor (:mir/predecessor incoming)
                                       :gmir/value (:mir/value incoming)})
                                    value)
                              :else value)))
                   {} instruction))
                instructions)}))))
  program)

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
            calls (filter #(= :mir/call (:mir/op %)) instructions)]
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
        (when (and (= :physical registers) (= :all-vregs frame-policy))
          (let [value-ops #{:mir/argument :mir/constant :mir/add :mir/subtract
                            :mir/multiply :mir/quotient :mir/bit-and :mir/bit-or
                            :mir/bit-xor :mir/shift-left :mir/shift-right-signed
                            :mir/shift-right-unsigned
                            :mir/f64-add :mir/f64-subtract :mir/f64-multiply
                            :mir/f64-divide :mir/f64-min :mir/f64-max
                            :mir/f64-sqrt :mir/f64-equal :mir/f64-less-than
                            :mir/f64-less-or-equal :mir/f64-greater-than
                            :mir/f64-greater-or-equal :mir/f64-unordered
                            :mir/equal :mir/less-than
                            :mir/greater-than :mir/less-or-equal
                            :mir/greater-or-equal :mir/call}]
            (doseq [[index instruction] (map-indexed vector instructions)
                    :when (contains? value-ops (:mir/op instruction))]
              (let [store (get instructions (inc index))]
                (when-not (and (= :mir/spill-store (:mir/op store))
                               (= (:mir/dst instruction) (:mir/src store)))
                  (reject! :unbacked-call-frame-value
                           {:function name :instruction instruction}))))
            (doseq [[index {:mir/keys [arguments] :as call}]
                    (map-indexed vector instructions)
                    :when (= :mir/call (:mir/op call))]
              (let [loads (when (>= index (count arguments))
                            (subvec instructions (- index (count arguments)) index))]
                (when-not (and (some? loads)
                               (= (count loads) (count arguments))
                               (every? #(= :mir/spill-load (:mir/op %)) loads)
                               (= arguments (mapv :mir/dst loads)))
                  (reject! :non-parallel-call-arguments
                           {:function name :call call}))))))
        (doseq [{:mir/keys [callee arguments] :as call} calls]
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

(defn- select-instruction [instruction]
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
              :gmir/callee :mir/callee
              :gmir/arguments :mir/arguments)
            (cond
              (= key :gmir/op) (keyword "mir" (name value))
              (= key :gmir/incomings)
              (mapv (fn [incoming]
                      {:mir/predecessor (:gmir/predecessor incoming)
                       :mir/value (:gmir/value incoming)})
                    value)
              :else value)))
   {} instruction))

(defn select-target
  "Select the closed GMIR operation set into target MIR, preserving vregs."
  [target program]
  (when-not (contains? targets target)
    (reject! :unsupported-target {:target target}))
  (gmir/validate! program)
  (validate!
   (if (= 3 (:gmir/version program))
     {:mir/version 3
      :mir/target target
      :mir/registers :virtual
      :mir/entry (:gmir/entry program)
      :mir/functions
      (mapv (fn [{:gmir/keys [name arity instructions]}]
              {:mir/name name :mir/arity arity
               :mir/instructions (mapv select-instruction instructions)})
            (:gmir/functions program))}
     {:mir/version (:gmir/version program)
      :mir/target target
      :mir/registers :virtual
      :mir/instructions (mapv select-instruction
                              (:gmir/instructions program))})))

(defn- sources [instruction]
  (concat (keep instruction [:mir/src :mir/input :mir/left :mir/right
                             :mir/test :mir/value])
          (when (vector? (:mir/arguments instruction))
            (:mir/arguments instruction))))

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

(defn- last-uses [instructions]
  (reduce-kv
   (fn [uses index instruction]
     (reduce #(assoc %1 %2 index) uses (filter gmir/vreg? (sources instruction))))
   {} instructions))

(defn- ordered-vregs [values]
  (sort-by (fn [value] (or (:gmir/id value) (str value))) values))

(defn- expire-assigned
  "Remove VALUES from STATE's assignment without returning a register that is
  still owned by another SSA value (the latter occurs after a dying-left
  destination coalesces onto its source register)."
  [state values]
  (let [expired (vec (ordered-vregs values))
        assigned (:assigned state)
        remaining (apply dissoc assigned expired)
        still-owned (set (vals remaining))
        freed (remove still-owned (map assigned expired))]
    (-> state
        (assoc :assigned remaining)
        (update :free into freed))))

(defn- entry-argument-plan
  "Materialize a function's ABI inputs as canonical self-markers followed by a
  parallel copy into allocator registers. Unused inputs need only their marker.
  Non-prefix arguments or more simultaneously used inputs than the allocator
  profile fail into the existing all-vreg path."
  [target instructions last-use temp-slot]
  (let [[arguments remaining] (split-with #(= :mir/argument (:mir/op %))
                                          instructions)]
    (when (some #(= :mir/argument (:mir/op %)) remaining)
      (reject! :spill-required {:problem :non-prefix-argument}))
    (let [arguments (vec arguments)
          remaining (vec remaining)
          allocator-registers (get physical-registers target)
          abi-registers (get call-argument-registers target)
          used (filterv #(contains? last-use (:mir/dst %)) arguments)]
      (when (> (count used) (count allocator-registers))
        (reject! :spill-required {:problem :entry-register-pressure}))
      (let [assigned (into {}
                           (map (fn [instruction register]
                                  [(:mir/dst instruction) register])
                                used allocator-registers))
            input-register (fn [instruction]
                             (or (get abi-registers (:mir/index instruction))
                                 (reject! :spill-required instruction)))
            markers (mapv #(assoc % :mir/dst (input-register %)) arguments)
            copies (mapv (fn [instruction]
                           {:mir/dst (get assigned (:mir/dst instruction))
                            :mir/src (input-register instruction)})
                         used)
            scheduled (schedule-parallel-copies copies temp-slot)
            owned (set (vals assigned))]
        {:argument-count (count arguments)
         :remaining remaining
         :assigned assigned
         :free (vec (remove owned allocator-registers))
         :instructions (into markers (:instructions scheduled))
         :used-temp? (:used-temp? scheduled)}))))

(defn- call-live-slots
  "Assign stable slots only to SSA values whose definition precedes a call and
  whose final use follows that call. Slots are ordered by definition, so the
  result is deterministic and independent of target register names."
  [instructions]
  (let [last-use (last-uses instructions)
        call-indexes (->> instructions
                          (keep-indexed (fn [index instruction]
                                          (when (= :mir/call (:mir/op instruction))
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
  (and (some #(= :mir/call (:mir/op %)) instructions)
       (not-any? #(contains? #{:mir/label :mir/branch-zero :mir/jump :mir/phi}
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
        slots (call-live-slots instructions)
        allocator-registers (get physical-registers target)
        argument-registers (get call-argument-registers target)
        return-register (get return-registers target)
        temp-slot (count slots)]
    (when (> (+ (count slots) 1) 4095)
      (reject! :spill-frame-too-large {:frame-slots (count slots)}))
    (let [entry (entry-argument-plan target instructions last-use temp-slot)]
      (letfn [(expire [state index just-defined]
                (let [expired (filter #(or (= index (get last-use %))
                                           (and (= just-defined %)
                                                (not (contains? last-use %))))
                                      (keys (:assigned state)))]
                  (expire-assigned state expired)))
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
               (if (= :mir/call op)
                 (let [state (ensure-sources state instruction arguments)
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
                       call-registers (subvec argument-registers 0 (count arguments))
                       copies (mapv (fn [value register]
                                      {:mir/dst register
                                       :mir/src (get-in state [:assigned value])})
                                    arguments call-registers)
                       scheduled (schedule-parallel-copies copies temp-slot)
                       call {:mir/op :mir/call :mir/dst return-register
                             :mir/callee (:mir/callee instruction)
                             :mir/arguments call-registers}
                       state (-> state
                                 (update :out into stores)
                                 (update :out into (:instructions scheduled))
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
                                           (if (gmir/vreg? value)
                                             (get-in state [:assigned value])
                                             value)))
                                  {} instruction)
                       state (update state :out conj allocated)]
                   (expire state index dst))))
             {:assigned (:assigned entry) :free (:free entry) :materialized #{}
              :used-temp? (:used-temp? entry) :out (:instructions entry)}
             (map-indexed (fn [offset instruction]
                            [(+ (:argument-count entry) offset) instruction])
                          (:remaining entry)))
            frame-slots (+ (count slots) (if (:used-temp? result) 1 0))]
        (validate-flat!
         {:mir/version version
          :mir/target target
          :mir/registers :physical
          :mir/frame-slots frame-slots
          :mir/instructions (:out result)}))))))

(defn- allocate-without-spills
  [{:mir/keys [version target registers instructions] :as program} merge-slots]
  (when-not (= :virtual registers)
    (reject! :registers-not-virtual program))
  (let [last-use (last-uses instructions)
        entry (entry-argument-plan target instructions last-use merge-slots)]
    (loop [index (:argument-count entry), remaining (:remaining entry)
           assigned (:assigned entry), free (:free entry)
           out (:instructions entry), used-temp? (:used-temp? entry)]
      (if-let [instruction (first remaining)]
        (let [srcs (filter gmir/vreg? (sources instruction))]
          (doseq [source srcs]
            (when-not (contains? assigned source)
              (reject! :use-before-definition instruction)))
          (let [dst (:mir/dst instruction)
                [assigned free]
                (if (gmir/vreg? dst)
                  (do
                    (when (contains? assigned dst)
                      (reject! :multiple-definition instruction))
                    (let [dying-left (when (and (gmir/vreg? (:mir/left instruction))
                                                (= index (get last-use
                                                              (:mir/left instruction))))
                                       (get assigned (:mir/left instruction)))
                          register (or (first free) dying-left)]
                      (when-not register
                        (reject! :spill-required instruction))
                      [(assoc assigned dst register)
                       (if (seq free) (vec (rest free)) free)]))
                  [assigned free])
                allocated (reduce-kv
                           (fn [result key value]
                             (assoc result key
                                    (if (gmir/vreg? value)
                                      (get assigned value)
                                      value)))
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
                state (expire-assigned {:assigned assigned :free free} expired)]
            (recur (inc index) (next remaining)
                   (:assigned state) (vec (:free state))
                   (conj out allocated) used-temp?)))
        (validate-flat!
         {:mir/version version
          :mir/target target
          :mir/registers :physical
          :mir/frame-slots (+ merge-slots (if used-temp? 1 0))
          :mir/instructions out})))))

(defn- spill-slots [instructions offset]
  (:slots
   (reduce (fn [{:keys [slots defined] :as state}
                {:mir/keys [dst] :as instruction}]
             (doseq [source (filter gmir/vreg? (sources instruction))]
               (when-not (contains? defined source)
                 (reject! :use-before-definition instruction)))
             (if (gmir/vreg? dst)
               (do
                 (when (contains? defined dst)
                   (reject! :multiple-definition instruction))
                 {:slots (assoc slots dst (+ offset (count slots)))
                  :defined (conj defined dst)})
               state))
           {:slots {} :defined #{}}
           instructions)))

(defn- allocate-with-spills
  [{:mir/keys [version target instructions] :as program} merge-dst-by-slot]
  (let [slots (spill-slots instructions 0)
        slot-count (count slots)
        [r0 r1] (get physical-registers target)
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
          (fn [{:mir/keys [op dst input left right test value callee arguments]
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

              :mir/merge-store
              (let [phi-dst (or (get merge-dst-by-slot (:mir/slot instruction))
                                (reject! :unknown-merge-slot instruction))]
                [(load-value instruction (:mir/src instruction) r0)
                 (store-value instruction phi-dst r0)])

              :mir/merge-load
              []

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

              :mir/branch-zero
              [(load-value instruction test r0)
               (assoc instruction :mir/test r0)]

              :mir/call
              (let [call-registers (subvec argument-registers 0 (count arguments))]
                (concat
                 (mapv (fn [value register]
                         (load-value instruction value register))
                       arguments call-registers)
                 [{:mir/op :mir/call
                   :mir/dst (get return-registers target)
                   :mir/callee callee
                   :mir/arguments call-registers}
                  (store-value instruction dst (get return-registers target))]))

              :mir/return
              [(load-value instruction value r0)
               (assoc instruction :mir/value r0)]

              (:mir/label :mir/jump) [instruction]
              (reject! :unsupported-spill-operation instruction)))
          instructions))}))))

(defn- allocate-flat
  "Allocate virtual MIR deterministically, inserting bounded stack-slot spills
  when the target scratch profile is exhausted."
  [program]
  (validate-flat! program)
  (let [{:keys [program merge-slots merge-dst-by-slot]} (lower-phis program)]
    (if (some #(= :mir/call (:mir/op %)) (:mir/instructions program))
      (allocate-with-spills program merge-dst-by-slot)
      (try
        (coalesce-phi-transports
         (allocate-without-spills program merge-slots)
         merge-slots)
        (catch #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) error
          (if (= :spill-required (:problem (ex-data error)))
            (allocate-with-spills program merge-dst-by-slot)
            (throw error)))))))

(defn allocate-registers
  "Allocate a legacy flat program or every function in a v3 module. A function
  containing a straight-line call stores only values live across that call and
  reloads them lazily. Complex control flow and excess register pressure retain
  the conservative all-vreg path."
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
                (let [calls? (some #(= :mir/call (:mir/op %)) instructions)
                      virtual {:mir/version 3 :mir/target target
                               :mir/registers :virtual
                               :mir/instructions instructions}
                      [allocated frame-policy]
                      (if (straight-line-call-program? instructions)
                        (try
                          [(allocate-call-live virtual) :call-live]
                          (catch #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) error
                            (if (= :spill-required (:problem (ex-data error)))
                              [(allocate-flat virtual) :all-vregs]
                              (throw error))))
                        [(allocate-flat virtual)
                         (if calls? :all-vregs :allocator)])]
                  {:mir/name name
                   :mir/arity arity
                   :mir/frame-slots (:mir/frame-slots allocated)
                   :mir/frame-policy frame-policy
                   :mir/instructions (:mir/instructions allocated)}))
              functions)}))
    (allocate-flat program)))
