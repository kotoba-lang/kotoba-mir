# Canonical MIR migration: source candidate

This is an incomplete source port, not a native-qualified release. The final
closure uses canonical `.kotoba` and an Amu selfhost-built and rebuilt compiler.
CLJK/CLJC/CLJS, NBB/KBB, Node, Clojure/Java/JVM/Graal and a C compiler, loader or
runtime are not final build, packaging or execution prerequisites. CDCI must
eventually run both its controller and gates as loaderless
`x86_64-linux-static` ELF artifacts.

## Owning source and dependency

The transcription reference is owning main
`2653e5f1413812248c84c33598a67c8ea1e1a3af`. Its complete 3,383-line
`src/kotoba/mir.cljk` and both existing suites remain byte-identical. The current
reference includes the fuel-charge and gas-charge offsets and the removal of
the obsolete hosted CI; that removal is not native qualification.

The supporting native modules explicitly depend on the canonical GMIR source
in [GMIR #42](https://github.com/kotoba-lang/kotoba-gmir/pull/42), inspected at
`b3fa31ec37151a8d8a2b460260a06605d64cd65e`. That dependency is draft/unmerged
and itself native-unqualified. No GMIR source is vendored here, no local overlay
is a lock update, and the existing hosted `deps.edn` is not a native resolver
recipe. Dependency integration, reviewed pins and Definition CIDs remain open.

[MIR #75](https://github.com/kotoba-lang/kotoba-mir/pull/75) contains useful
historical dual-runtime readings in CLJK. Those readings do not satisfy the
final canonical source contract or establish native execution. This source
candidate neither overwrites that draft nor uses its host runtime as an oracle.

## Present supporting source

| Module | Scope |
| --- | --- |
| `catalog.kotoba` | All 104 instruction keysets, both targets, all register banks, 37 runtime offsets, 8 capability offsets, versions, bounds, derived atomic/dequant operation sets, privileged registers and allocator pool |
| `outcome.kotoba` | Typed MIR refusals and lossless GMIR refusal adaptation: phase, problem, message and complete data |
| `registers.kotoba` | Physical register predicate and saved-register scan over every nested collection and map key, returning unique registers in preserved-bank order |
| `flat.kotoba` | Flat virtual/physical validation, exact fields and version exclusions, ordered profile/bound/ABI checks, labels and v2 GMIR projection |

IR and refusal data use GMIR's nominal nodes, separate namespace/name text and
paged children. Large programs and strings are not flattened into bounded
documents. Catalog lists represent named lookup, membership or explicit ABI
order; their row positions are not new wire indices.

`kotoba.mir.flat/validate!` validates a **flat component**, including the flat
version 3 form used inside a module. It is not the public module dispatcher.
There is no canonical `src/kotoba/mir.kotoba` root yet. It returns the original
input node on success and a typed full-data refusal on failure. Atom tags alone
do not establish nominal representation validity; a final recursive shape pass
runs after semantic checks. This pass adds `:non-canonical-value` for invalid
nominal values without replacing an earlier semantic refusal.

### Explicit API and bug-fix changes

* Public data maps/sets become typed named tables; queries return `Option`.
  Unknown lookup remains distinct from a real empty register sequence. Unknown
  target pool/privileged queries retain the reference's empty concatenation
  result; this does not admit that target to validation.
* Throwing APIs become `Result` values. Every native caller must propagate and
  consume these results. A GMIR error keeps its GMIR phase and projected input;
  it is not reduced to a MIR problem keyword.
* The owning v2 virtual adapter has a closed partial key `case` that omits
  modern fields such as `input`, `rodata-encoding`, and `function`. The new
  adapter renames every already-validated MIR field to GMIR, excludes only
  `context-offset`, and converts phi incoming keys. Modern instructions reach
  GMIR validation rather than a host unmatched-case exception. This is an
  explicit repair, not a claim of exception parity with the broken adapter.
* The reference's runtime/capability count domain and list/vector sequential
  equality are preserved. Unsupported scalar argument counts produce typed
  invalid-call refusals instead of a host count exception. String counts use
  UTF-16 units, including two units for an astral scalar. Physical ABI checks
  still require the exact ordered register sequence.
* The generic register scan preserves the reference's `keep` behavior: nil
  fields are skipped, and argument/parameter children are scanned there only
  for vectors. Existing admission holes are not an allocator permission or a
  reason to silently narrow accepted input during this transcription.
* A non-sequential scalar saved-register input produces a full-data
  `:non-sequential-instructions` refusal rather than a host sequence exception.

These representation/API changes require native parser, caller, hash/resolver
and CID migration. Name coverage alone is not compatibility or parity proof.

## Whole public scope remains required

All 29 original public names and their complete behavior remain acceptance
scope. Supporting source represents these 24 names:

```
allocator-pool call-argument-registers capability-argument-registers
capability-context-offsets instruction-keysets kernel-atomic-ops
kernel-dequant-dot-maximum kernel-dequant-dot-operations kernel-dot-f32-maximum
kernel-window-maxima kernel-window-operations leaf-registers physical-registers
preserved-registers privileged-argument-registers return-registers
runtime-argument-registers runtime-context-offsets saved-registers
slice-item-limit slice-operations supported-versions targets version
```

These five public APIs are still incomplete or unconnected:

```
validate! select-target allocate-registers
counted-self-recur-plan counted-self-recur-plans
```

Remaining behavior includes the complete v3 module/call graph and frame checks,
symbolic reentry transport, stack argument profiles, target selection and
exclusions, latency/dependency scheduling, zero-equality fusion, all selected
operation optimizations, phi lowering and parallel copies, safe coalescing,
CFG/dominance/liveness, all allocator/spill/frame policies, and counted fuel
analysis. No conservative-only replacement or stub root closes this scope.
The adopted Amu compiler core/lineage, frontend, lowering, optimizer, backend
and complete full19 Embench workload must be preserved through integration.

## Evidence and open gates

Two self-check entry sources are present:

* `kotoba.mir-catalog-cases/main`: complete table counts/lookup/uniqueness,
  banks, derived operation families, offsets, pool truthiness/order, nested/map
  key register scanning, unknowns and full refusal adaptation.
* `kotoba.mir-flat-cases/main`: all 104 instruction rows, every required-field
  removal and an extra field per row; all 37 runtime, 55 privileged and 8
  capability ABI rows; list/vector/count rules; version and first-refusal
  ordering; labels/frames; repaired v2 projection and nominal representation.

Both entries are **uncompiled and unexecuted**. They are not registered as a
replacement CI and do not replace the full upstream positive/refusal,
authority, allocation, fuel, stack, cleanup and large-input corpus.

Limited source-data inspection compares every literal table row against the
pinned Git data and reads source forms for imports/arity, schema/record use,
type positions, lexical names and forbidden host forms. It checks that all 30
reference flat refusal names remain present. It does not execute MIR, GMIR,
the compiler, a generator, an oracle, or tests, and is not the owning EDN reader
or a typechecker.

No qualified independent compiler ELF entry has been established for this
candidate. Native execution is authorized; the compiler entry is the missing
prerequisite. A raw seed requiring a C loader, a hand-written ELF probe or a
host-backed wrapper cannot supply it. Native reader/admission, compilation,
all positive/refusal/authority/resource execution, whole native self-rebuild
and fixed point, owning main/lock/CID integration and native CDCI gate/controller
qualification remain open. Static source inspection does not close any of
these gates.
