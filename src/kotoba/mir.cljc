(ns kotoba.mir
  "Closed target-selected Machine IR v1/v2 and deterministic allocation."
  (:require [kotoba.gmir :as gmir]))

(def version 2)
(def supported-versions #{1 2})
(def targets #{:x86-64 :aarch64})

(def physical-registers
  {:x86-64 [:x86-64/rax :x86-64/rcx :x86-64/rdx :x86-64/r8]
   :aarch64 [:aarch64/x0 :aarch64/x1 :aarch64/x2 :aarch64/x3]})

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
   :mir/equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/less-than #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/greater-than #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/less-or-equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/greater-or-equal #{:mir/op :mir/dst :mir/left :mir/right}
   :mir/spill-load #{:mir/op :mir/dst :mir/slot}
   :mir/spill-store #{:mir/op :mir/src :mir/slot}
   :mir/label #{:mir/op :mir/id}
   :mir/branch-zero #{:mir/op :mir/test :mir/target}
   :mir/jump #{:mir/op :mir/target}
   :mir/phi #{:mir/op :mir/dst :mir/incomings}
   :mir/return #{:mir/op :mir/value}})

(def ^:private v1-operations
  (disj (set (keys instruction-keysets)) :mir/phi))

(def ^:private v2-operations
  (set (keys instruction-keysets)))

(defn- operations-for [program-version]
  (case program-version
    1 v1-operations
    2 v2-operations
    #{}))

(defn- physical-register? [target value]
  (contains? (set (get physical-registers target)) value))

(defn validate!
  "Validate virtual or physical MIR and return it unchanged."
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
                   (contains? #{:mir/spill-load :mir/spill-store} op))
          (reject! :spill-in-virtual-program instruction))
        (doseq [register (keep instruction [:mir/dst :mir/src :mir/left :mir/right :mir/test])]
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

(defn select-target
  "Select the closed GMIR operation set into target MIR, preserving vregs."
  [target program]
  (when-not (contains? targets target)
    (reject! :unsupported-target {:target target}))
  (gmir/validate! program)
  (validate!
   {:mir/version (:gmir/version program)
    :mir/target target
    :mir/registers :virtual
    :mir/instructions
    (mapv (fn [instruction]
            (reduce-kv
             (fn [out key value]
               (assoc out
                      (case key
                        :gmir/op :mir/op
                        :gmir/dst :mir/dst
                        :gmir/index :mir/index
                        :gmir/value :mir/value
                        :gmir/left :mir/left
                        :gmir/right :mir/right
                        :gmir/id :mir/id
                        :gmir/test :mir/test
                        :gmir/target :mir/target
                        :gmir/incomings :mir/incomings)
                      (cond
                        (= key :gmir/op) (keyword "mir" (name value))
                        (= key :gmir/incomings)
                        (mapv (fn [incoming]
                                {:mir/predecessor (:gmir/predecessor incoming)
                                 :mir/value (:gmir/value incoming)})
                              value)
                        :else value)))
             {} instruction))
          (:gmir/instructions program))}))

(defn- sources [instruction]
  (keep instruction [:mir/src :mir/left :mir/right :mir/test :mir/value]))

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
     :merge-slots (count phis)}))

(defn- last-uses [instructions]
  (reduce-kv
   (fn [uses index instruction]
     (reduce #(assoc %1 %2 index) uses (filter gmir/vreg? (sources instruction))))
   {} instructions))

(defn- allocate-without-spills
  [{:mir/keys [version target registers instructions] :as program} merge-slots]
  (when-not (= :virtual registers)
    (reject! :registers-not-virtual program))
  (let [last-use (last-uses instructions)
        available (get physical-registers target)]
    (loop [index 0, remaining instructions, assigned {}, free available, out []]
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
                    (when-not (seq free)
                      (reject! :spill-required instruction))
                    [(assoc assigned dst (first free)) (vec (rest free))])
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
                expired (->> (keys assigned)
                             (filter #(= index (get last-use %)))
                             (sort-by str))
                free (into free (map assigned expired))
                assigned (apply dissoc assigned expired)]
            (recur (inc index) (next remaining) assigned (vec free)
                   (conj out allocated))))
        (validate!
         {:mir/version version
          :mir/target target
          :mir/registers :physical
          :mir/frame-slots merge-slots
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
  [{:mir/keys [version target instructions] :as program} merge-slots]
  (let [slots (spill-slots instructions merge-slots)
        slot-count (+ merge-slots (count slots))
        [r0 r1] (get physical-registers target)]
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
      (validate!
        {:mir/version version
        :mir/target target
        :mir/registers :physical
        :mir/frame-slots slot-count
        :mir/instructions
        (vec
         (mapcat
          (fn [{:mir/keys [op dst left right test value] :as instruction}]
            (case op
              (:mir/argument :mir/constant)
              [(assoc instruction :mir/dst r0)
               (store-value instruction dst r0)]

              :mir/merge-store
              [(load-value instruction (:mir/src instruction) r0)
               {:mir/op :mir/spill-store :mir/src r0 :mir/slot (:mir/slot instruction)}]

              :mir/merge-load
              [{:mir/op :mir/spill-load :mir/dst r0 :mir/slot (:mir/slot instruction)}
               (store-value instruction dst r0)]

              (:mir/add :mir/subtract :mir/multiply :mir/quotient
               :mir/bit-and :mir/bit-or :mir/bit-xor
               :mir/equal :mir/less-than :mir/greater-than
               :mir/less-or-equal :mir/greater-or-equal)
              [(load-value instruction left r0)
               (load-value instruction right r1)
               {:mir/op op :mir/dst r0 :mir/left r0 :mir/right r1}
               (store-value instruction dst r0)]

              :mir/branch-zero
              [(load-value instruction test r0)
               (assoc instruction :mir/test r0)]

              :mir/return
              [(load-value instruction value r0)
               (assoc instruction :mir/value r0)]

              (:mir/label :mir/jump) [instruction]
              (reject! :unsupported-spill-operation instruction)))
          instructions))}))))

(defn allocate-registers
  "Allocate virtual MIR deterministically, inserting bounded stack-slot spills
  when the target scratch profile is exhausted."
  [program]
  (validate! program)
  (let [{:keys [program merge-slots]} (lower-phis program)]
    (try
      (allocate-without-spills program merge-slots)
      (catch #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) error
        (if (= :spill-required (:problem (ex-data error)))
          (allocate-with-spills program merge-slots)
          (throw error))))))
