(require '[kotoba.mir :as mir]
         '[kotoba.gmir :as gmir])

(def scalar-call-module
  {:gmir/version 3 :gmir/entry 'main
   :gmir/functions
   [{:gmir/name 'add-one :gmir/arity 1
     :gmir/instructions
     [{:gmir/op :gmir/argument :gmir/dst (gmir/vreg 0) :gmir/index 0}
      {:gmir/op :gmir/constant :gmir/dst (gmir/vreg 1) :gmir/value 1}
      {:gmir/op :gmir/add :gmir/dst (gmir/vreg 2) :gmir/left (gmir/vreg 0) :gmir/right (gmir/vreg 1)}
      {:gmir/op :gmir/return :gmir/value (gmir/vreg 2)}]}
    {:gmir/name 'main :gmir/arity 1
     :gmir/instructions
     [{:gmir/op :gmir/argument :gmir/dst (gmir/vreg 0) :gmir/index 0}
      {:gmir/op :gmir/constant :gmir/dst (gmir/vreg 1) :gmir/value 10}
      {:gmir/op :gmir/call :gmir/dst (gmir/vreg 2) :gmir/callee 'add-one
       :gmir/arguments [(gmir/vreg 0)]}
      {:gmir/op :gmir/add :gmir/dst (gmir/vreg 3) :gmir/left (gmir/vreg 1) :gmir/right (gmir/vreg 2)}
      {:gmir/op :gmir/return :gmir/value (gmir/vreg 3)}]}]})

(doseq [target mir/targets]
  (let [caller (second (:mir/functions
                        (->> scalar-call-module
                             (mir/select-target target)
                             mir/allocate-registers)))
        ins (:mir/instructions caller)]
    (println "---" target "frame" (:mir/frame-slots caller) "---")
    (doseq [[i x] (map-indexed vector ins)]
      (println i (:mir/op x)
               (select-keys x [:mir/dst :mir/src :mir/slot :mir/value])))))
