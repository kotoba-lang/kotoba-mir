# ADR 0039: the Kotoba route runs MIR over `kotoba.form`

Status: accepted. Date: 2026-10-01.

## Context

`kotoba.mir` is the last host-only stage between GMIR and machine code: target
selection, register allocation, scheduling and the validators are all written
against Clojure maps, sets and vectors, with `ex-info` for refusals. A native
compiler that builds itself needs the same stage to run as Kotoba, and Kotoba
has no persistent maps, no `sort-by`, no destructuring of maps and no catchable
exceptions. `kotoba.form` (a typed, recursive s-expression record) is the
carrier the rest of the selfhost work uses for exactly that, and `kotoba.gmir`
already exports Form-returning functions.

## Decision

Every public function keeps its host body byte-for-byte and gains a Kotoba
twin in the same `#?(:kotoba ... :default ...)` form (`#?(:kotoba nil :default
...)` for host-only helpers). On the Kotoba route:

* **Data are Forms.** An instruction is a map form, a program a map form, a
  register list a vector form. The tables (`physical-registers`,
  `runtime-context-offsets`, ...) are exported as functions returning a Form
  read from EDN text, because a Kotoba `def` cannot hold a map of vectors. The
  103-entry instruction key-set table is additionally available as a `cond`
  over operation groups, so the validator never reads 12 KB of EDN per
  instruction.
* **Refusals are data first.** The host throws at the first problem; the twin
  computes it (`validate-problem`, `select-target-result`,
  `allocate-registers-result`) and the public function (`validate!`,
  `select-target`, `allocate-registers`) aborts with the same keyword. Checks
  run in the host's order, so the problem named is the host's problem.
  The host gains `validate-problem`, `select-target-result` and
  `allocate-registers-result` with the same shape, so the two routes can be
  compared on identical programs.
* **`try/catch :spill-required` becomes a state flag.** The linear scan
  (`allocate-without-spills`) carries one state map; a step that would throw
  sets `:problem` and every caller stops at it. `allocate-with-policy-result`
  then falls back to the conservative all-vreg path exactly where the host
  catches `:spill-required`, and propagates every other problem.
* **Kotoba idioms the code is written around.** A `let` may not rebind a name;
  a function holds one loop (siblings and loops in binding position hit the
  loop-lifting pass), so loops live in small named functions; no call that can
  abort precedes `recur` (hence result maps instead of `reject!` inside loops);
  long `or` chains are split because desugared nesting is bounded by the host
  stack.
* **Dominator analysis stays host-only.** `cfg-dominator-*` and
  `cfg-dominates?` are used by the tests, not by allocation, so they have no
  twin.

## Consequences

* `amu check src/kotoba/mir.cljk` admits the module. The margin is narrow by
  construction: the linked project (mir + gmir + form) is 1013 functions
  against the 1024-function admission limit of `kotoba.compiler.project`, so
  a dependency growing by a dozen functions needs either a smaller `mir` or a
  higher limit.
* The host route is unchanged: the full `kotoba.mir-test` suite gives the same
  result before and after.
* Callers that hold host maps (`kotoba.native.machine-ir`) keep calling the
  same names with the same arities; they become Kotoba-admissible when they
  hold Forms, which is their own port.
