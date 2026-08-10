(ns kotoba.mir
  "Closed target-selected Machine IR v1 and deterministic allocation."
  (:require [kotoba.gmir :as gmir]))

(def version 1)
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
   :mir/return #{:mir/op :mir/value}})

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
                 (= 1 version)
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
      (let [op (:mir/op instruction)]
        (when-not (= (get instruction-keysets op) (set (keys instruction)))
          (reject! :non-canonical-instruction instruction))
        (when (and (= :virtual registers)
                   (contains? #{:mir/spill-load :mir/spill-store} op))
          (reject! :spill-in-virtual-program instruction))
        (doseq [register (keep instruction [:mir/dst :mir/src :mir/left :mir/right :mir/test])]
          (when-not (register? register)
            (reject! :register-profile-violation instruction)))
        (when (and (= op :mir/return) (not (register? (:mir/value instruction))))
          (reject! :register-profile-violation instruction))
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
          (reject! :unresolved-target {:target branch-target})))))
  program)

(defn select-target
  "Select the closed GMIR operation set into target MIR, preserving vregs."
  [target program]
  (when-not (contains? targets target)
    (reject! :unsupported-target {:target target}))
  (gmir/validate! program)
  (validate!
   {:mir/version version
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
                        :gmir/target :mir/target)
                      (if (= key :gmir/op)
                        (keyword "mir" (name value))
                        value)))
             {} instruction))
          (:gmir/instructions program))}))

(defn- sources [instruction]
  (keep instruction [:mir/src :mir/left :mir/right :mir/test :mir/value]))

(defn- last-uses [instructions]
  (reduce-kv
   (fn [uses index instruction]
     (reduce #(assoc %1 %2 index) uses (filter gmir/vreg? (sources instruction))))
   {} instructions))

(defn- allocate-without-spills
  [{:mir/keys [target registers instructions] :as program}]
  (validate! program)
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
          :mir/frame-slots 0
          :mir/instructions out})))))

(defn- spill-slots [instructions]
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
                 {:slots (assoc slots dst (count slots))
                  :defined (conj defined dst)})
               state))
           {:slots {} :defined #{}}
           instructions)))

(defn- allocate-with-spills
  [{:mir/keys [target instructions] :as program}]
  (let [slots (spill-slots instructions)
        slot-count (count slots)
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
  (try
    (allocate-without-spills program)
    (catch #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) error
      (if (= :spill-required (:problem (ex-data error)))
        (allocate-with-spills program)
        (throw error)))))
