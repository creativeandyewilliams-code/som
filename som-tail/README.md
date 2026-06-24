# som-tail — TAIL Lean formalization

Lean 4 formalization of the load-bearing mathematics in
`som_necessity_program_v1.tex`, targeting ledger items N1–N5 (§9).

## Structure

| File | Tier | Ledger claim |
|---|---|---|
| `SomTail/Witness.lean` | A | N1 — first-order non-descent |
| `SomTail/Complexity.lean` | B | N2 — tail is Σ⁰₂ |
| `SomTail/UpperBound.lean` | C | N3 — ACA upper bound |
| `SomTail/Coding.lean` | D | N4 — Route-A coding |
| `SomTail/Reversal.lean` | D | N5 — reversal (open obligation, `sorry`) |
| `scripts/verify_structure.py` | — | kernel-independent pre-check |
| `scripts/PrintAxioms.lean` | — | `#print axioms` disclosure |
| `CERTIFICATE.md` | — | adequate build certificate |

## Building locally

```bash
elan toolchain install $(cat lean-toolchain)
lake exe cache get          # fetch prebuilt Mathlib (highly recommended)
python3 scripts/verify_structure.py SomTail
lake build
lake env lean scripts/PrintAxioms.lean
```

## Companion documents

- `som_necessity_program_v1.tex` — source of all mathematical claims
- `som_control_limits_main_v4.tex` / `som_control_limits_supplement_v4.tex`
  — first-order non-descent background

## Honest accounting

Exactly **one** `sorry` exists in this development: `reversal` in
`Reversal.lean` (N5, the open obligation). Tiers A and B carry no `sorry`.
The `CERTIFICATE.md` records the structural pre-check output verbatim and
maps every load-bearing theorem to its ledger ID.
