# kotoba-mir

Kotoba target Machine IR: target-selected instructions with explicit virtual or
physical register state.

**Tier**: `T0`  **Role**: `contract`

## Owns

- MIR v1 target and instruction contracts plus the versioned MIR v2 phi
  extension;
- GMIR-to-MIR target selection for the matching closed operation set;
- deterministic allocation onto the v1 scratch-register profiles, with bounded
  stack-slot spills when live values exceed the physical profile;
- deterministic v2 phi lowering with direct edge moves for acyclic multi-phi
  joins, one reusable temporary frame slot for cyclic parallel copies, and
  destination-slot coalescing in the general spill path;
- fail-closed validation of virtual and physical MIR.

## Does not own

- KIR or KIR-to-GMIR lowering;
- instruction encoding or branch-byte layout;
- ABI prologues, calls, artifact identity, or object formats.

## Dependency direction

```text
kotoba-mir -> kotoba-gmir
```

No target backend is imported by this contract.

## Test

```bash
clojure -M:test
```
