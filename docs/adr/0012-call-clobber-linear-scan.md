# ADR 0012: Call clobbers in the linear scanner

## Status

Accepted.

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

## Consequences

A caller with one call and one `if` no longer stores every SSA value. Live
across values that fit in the preserved tier do not occupy a slot. Tests
must execute the call ABI, not only count encodings: a hasty proportional
spill at the call site already produced silent wrong code on a branch.
