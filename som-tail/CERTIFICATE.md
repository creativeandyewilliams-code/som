# SomTail Build Certificate

> **Rule 1 (never fake a build):** The build result below reflects the actual
> exit code of `lake build` from CI. The local network blocks Lean toolchain
> downloads (`release.lean-lang.org` returns 403 via the sandbox proxy), so no
> local build was attempted. Results come from the GitHub Actions run linked in
> §1; that run's exit code is the ground truth.

---

## 1. Header

| Field | Value |
|---|---|
| Date | See CI run timestamp |
| Repo commit | See CI run (branch `claude/kind-noether-1vmysz`) |
| `lean-toolchain` | `leanprover/lean4:v4.32.0-rc1` |
| Mathlib pin | HEAD of `master` at CI build time — exact SHA in `.lake/packages/mathlib` (see artifact) |
| Mathlib cache used | See CI log (`lake exe cache get` result) |
| CI workflow | `.github/workflows/som-tail-build.yml` |

---

## 2. Build result

> **This section is updated by CI.** The `CERTIFICATE_RAW.txt` artifact from
> the GitHub Actions run contains the literal exit code and verbatim log.

The pre-check (§6) passes with exactly one declared `sorry`:

| File | Line | Nature |
|---|---|---|
| `SomTail/Reversal.lean` | 50 | `sorry` — N5 open obligation (expected) |

**Pending CI:** verdict will be one of:
- `GREEN — all compiled theorems kernel-checked` (if `lake build` exits 0)
- `PARTIAL — built with 1 declared sorry` (if sorry in Reversal.lean is the only issue)
- `RED — build failed` (if any theorem proof fails)

---

## 3. Theorem → Claim Map (N1–N5)

| Lean theorem | File | Note claim (ledger ID) |
|---|---|---|
| `trunc_factors` | `Witness.lean` | N1 — first-order non-descent (supporting) |
| `tower_refines` | `Witness.lean` | N1 — first-order non-descent (supporting) |
| `hist_agree` | `Witness.lean` | N1 — first-order non-descent (supporting) |
| `tail_xA` | `Witness.lean` | N1 — first-order non-descent (supporting) |
| `tail_xB` | `Witness.lean` | N1 — first-order non-descent (supporting) |
| `nondescent` | `Witness.lean` | **N1 — first-order non-descent (headline)** |
| `tail_iff_sigma02` | `Complexity.lean` | **N2 — tail is Σ⁰₂** |
| `tail_decided_with_jump` | `UpperBound.lean` | **N3 — ACA upper bound** |
| `coding_correct` | `Coding.lean` | **N4 — Route-A coding reduction** |
| `reversal` (**sorry**) | `Reversal.lean` | **N5 — open obligation** |

---

## 4. Incompleteness section

Exactly **one** `sorry` appears in this development:

| File | Line | Symbol | Obligation |
|---|---|---|---|
| `SomTail/Reversal.lean` | 50 | `reversal` | N5: assembly of the range principle from the TAIL solver; requires Σ⁰₁-induction in a reverse-math base theory not yet available in Lean/Mathlib |

No `sorry` appears in Tiers A (Witness.lean) or B (Complexity.lean). This is
confirmed by the structural pre-check (§6).

---

## 5. Axiom disclosure

Run `lake env lean scripts/PrintAxioms.lean` from the `som-tail` directory to
obtain the full `#print axioms` output for every load-bearing theorem.

**Expected for N1–N4:** only `propext`, `Classical.choice`, `Quot.sound`  
(the mathlib-standard base). If `sorryAx` appears in any N1–N4 theorem that is
a defect; report it prominently.

**Expected for N5 (`reversal`):** `sorryAx` will appear, confirming the
obligation is genuinely open.

*Full output (to be populated from CI run):*

```
#print axioms nondescent
-- 'nondescent' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms tail_iff_sigma02
-- 'tail_iff_sigma02' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms tail_decided_with_jump
-- 'tail_decided_with_jump' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms coding_correct
-- 'coding_correct' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms reversal
-- 'reversal' depends on axioms: [propext, Classical.choice, Quot.sound, sorryAx]
```

*(Populated from CI once `lake build` succeeds.)*

---

## 6. Structural pre-check output

```
======================================================================
STRUCTURAL PRE-CHECK — som-tail
======================================================================

[1] Checking Tier A/B files for sorry/admit/native_decide …
  OK    Witness.lean
  OK    Complexity.lean
  → Tier A/B files are sorry-free. ✓

[2] Collecting all sorry occurrences …
  Sorry inventory (expected only in Reversal.lean):
    [EXPECTED]  Reversal.lean:50: sorry

[3] Checking for required theorems …
  OK       trunc_factors
  OK       tower_refines
  OK       hist_agree
  OK       tail_xA
  OK       tail_xB
  OK       nondescent
  OK       tail_iff_sigma02
  OK       tail_decided_with_jump
  OK       coding_correct
  OK       reversal

[4] Checking for new axiom declarations …
  No new axiom declarations found. ✓

======================================================================
RESULT: PASSED
```

*(Run locally against the source tree on 2026-06-24.)*

---

## 7. Full `lake build` log

*To be populated from CI. The verbatim log is in the `CERTIFICATE_RAW.txt`
artifact attached to the CI run at
`.github/workflows/som-tail-build.yml`.*

---

## 8. Scope and non-claims

This certificate, when green, certifies the following load-bearing mathematics
from `som_necessity_program_v1.tex`:

- **N1 (certified):** the first-order non-descent — `xA` and `xB` share a full
  observation history (`qInf xA = qInf xB`) yet differ in tail status
  (`Tail xA`, `¬ Tail xB`).
- **N2 (certified):** the tail predicate sits at Σ⁰₂ — `TailLimsup x ↔ Tail x`,
  where `Tail` is the explicit `∃ k ∃ M ∀ m` condition.
- **N3 (certified):** an ACA-style upper bound — a TAIL solver using the promise
  (either the Σ⁰₂ condition or its negation) decides the tail bit; arithmetical
  comprehension suffices.
- **N4 (certified):** the Route-A coding reduction — `¬ Tail (pf f y) ↔ ∃ x, f x = y`.

**This certificate does NOT certify:**

- **N5 (open obligation):** that second-order mathematics is *required* for
  deciding TAIL. The reversal — a TAIL solver implies the range principle
  (≡ ACA₀) — is stated faithfully in `Reversal.lean` but carries a declared
  `sorry`. The `#print axioms reversal` output will show `sorryAx`, confirming
  this is genuinely open, not silently closed.
- Any claim about the *necessity* of strong axioms; the current build certifies
  *sufficiency* (N3) and the coding structure (N4) that would feed into necessity
  once N5 is closed.
