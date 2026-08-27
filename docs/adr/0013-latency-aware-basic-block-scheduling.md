# ADR 0013: Latency-aware basic-block scheduling

## Decision

Schedule only consecutive SSA segments made from pure, non-trapping integer
operations. All other MIR operations are hard barriers and retain their exact
position relative to surrounding segments.

Within a segment, a deterministic list scheduler preserves producer-consumer
dependencies. It prefers the longest remaining modeled dependency path, then
the original instruction position. A conceptual issue cycle allows independent
work to fill a modeled multiply dependency gap.

An already-adjacent, single-use AArch64 multiply-add/subtract candidate is also
a barrier pair. The downstream MC selector can fuse it to MADD/MSUB only while
it remains adjacent, so local scheduling must not separate it.

The per-target latency tables are conservative compiler heuristics, not
microarchitecture measurements. This ADR therefore qualifies deterministic
instruction scheduling, but does not claim a runtime speed improvement. Native
execution evidence belongs in the downstream Amu integration.
