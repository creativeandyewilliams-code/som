# som — Bounded global-coherence certificate

A Lean 4 formalization of "Bounded formal certification of a globally
coherent hypothesis": a finite, decidable certificate semantics for a
claim-status ledger (type consistency, compositional closure, and
bounded-defeater freedom).

- `docs/bounded-gch-proof.md` — the expanded, fully spelled-out proof.
- `BoundedGCH/Cert.lean` — the Lean formalization: definitions, decidability
  instances, and the soundness / defeater-detection / budget-monotonicity
  theorems.
- `.github/workflows/lean-build.yml` — the build certificate: CI installs
  the pinned Lean toolchain and runs `lake build`; a green run is the
  machine-checked proof that every theorem in `Cert.lean` type-checks with
  no `sorry`.

## Building locally

```
elan toolchain install $(cat lean-toolchain)
lake build
```
