# kotoba-mir

Kotoba target Machine IR: target-selected instructions with explicit virtual or
physical register state.

**Tier**: `T0`  **Role**: `contract`

## Owns

- MIR v1 target and instruction contracts;
- GMIR-to-MIR target selection for the closed v1 operation set;
- deterministic allocation onto the v1 scratch-register profiles, with bounded
  stack-slot spills when live values exceed the physical profile;
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
