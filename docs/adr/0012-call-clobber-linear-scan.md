# ADR 0012: Call clobbers in the linear scanner

## Status

Accepted, and **defective as implemented**. Do not advance amu onto this pin.

Measured 2026-08-18 through amu, which executes native code:

| kotoba-mir | amu suite |
|---|---|
| `8872a54` (before) | 1094 tests, 0 failures |
| `7f7c556` (this) | 1096 tests, **62 failures** |

60 of them are string search, split **30 AArch64 / 30 x86-64**. An even split
across two independent encoders puts the fault in the shared allocator.

```
(defn main [] (if (string-contains? "abcdef" "def") 1 0))   ; => 0, expected 1
```

`string-replace-all` returns wrong content and wrong byte lengths, and one
multi-byte case traps. Cases expecting "absent" largely still pass, so the
search loop fails to *find* rather than failing outright.

Neither this repository's suite nor kotoba-native's can report any of it.
Both inspect encodings, frame policy and slot counts; neither runs a compiled
program, so no result either can produce distinguishes this implementation
from a correct one. The Consequences section below anticipated exactly this
and it still happened.

## Context

ADR 0006 materializes only values live across a straight-line call. ADR 0011
spills what does not fit, but only on the no-call path. A function that
contained both a call and a label, branch, jump, or phi still took
`allocate-with-spills`: every SSA value received a stack slot. On a 24-live
caller that differed from its straight-line twin by one `if`, that was 99
slots and 325 instructions against 24 slots and 190.

The hardware ABI already restores the preserved tier across a call. The
allocator's on-demand pool (iteration 06) already offers that tier. The
scanner did not use it at a call, so the extra control flow paid all-vreg.

## Decision

The linear scanner accepts calls. The non-leaf pool is scratch then
preserved. Values whose last use follows a call prefer a preserved register
at their definition. Remaining live caller-saved values are stored at their
definition — the store dominates every reload, including an arm that does
not contain the call — then dropped from the assignment. The call uses the
ABI registers. A new result that is itself live across a later call moves
into the preserved tier when a register is free.

Straight-line callers keep the ADR 0006 `allocate-call-live` path. The
linear scanner is the path for control flow. Leftover pressure still fails
into all-vreg.

Physical functions produced this way declare `:call-live`. `:all-vregs`
remains the fallback.

`back-edge?` (added 2026-08-18) sends a call-containing function with a
backward `:mir/jump` or `:mir/branch-zero` to `:all-vregs` before the scanner
sees it. `last-uses` records only the highest instruction *index* at which a
vreg is a source -- it reads no label and no branch target -- so a value's
interval ends at its textually last use. That is sound while the scanner only
sees straight-line functions, where textual order is execution order; a back
edge re-reads a value after its register has been given away. This is the
`:cfg-liveness false` claim below, stated as a defect rather than as a
limitation.

**It is necessary and not sufficient, measured rather than assumed: 62
failures become 61.** It fixes
`let-composes-with-recursion-within-the-fuel-budget` and does not touch string
search, so whatever loop `string-contains?` and `string-replace-all` lower to
is not a backward jump this predicate sees. The rest of the fault is not yet
located. Do not read the predicate as the fix.

A second located hole, independent of a back edge: `last-uses` is still
textual, so a reload on the then-arm keeps the value in `:assigned` for the
else-arm, which never executed that load and then reads a leftover
callee-saved register. Store-at-definition does not prevent this. At every
label after the entry, backed values that are currently assigned are dropped
so the next use in that block loads them again. Unbacked values stay: their
definition dominates the split. This is not a rebuild of the free lists on
every label -- that scramble broke phi coalescing on leaf bodies.

Encoding test: `v3-else-arm-reloads-a-value-the-then-arm-already-reloaded`.
That is the same class of evidence this repository already had, and it is
not an amu execution. Do not advance amu until `string-contains?` is
measured there.

Shapes measured correct, so the defect is narrower than "calls plus control
flow": a call with ten values live across it read in a branch arm; two calls
with the first result live across the second; a call result used directly as
a branch condition; `kernel_call_branch` and `kernel_call_deep_branch`.

## Consequences

A caller with one call and one `if` no longer stores every SSA value. Live
across values that fit in the preserved tier do not occupy a slot. Tests
must execute the call ABI, not only count encodings: a hasty proportional
spill at the call site already produced silent wrong code on a branch.
