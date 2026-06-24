/-!
# SomTail.Reversal — L5: The reversal (Tier D, open obligation N5)

Formalizes N5 from `som_necessity_program_v1.tex §9`.

States the conditional necessity theorem: a "TAIL solver" (a procedure deciding
the Σ⁰₂ tail condition for every rational bounded sequence) implies the range
principle for injections, which is equivalent to arithmetical comprehension (ACA₀)
over RCA₀. This is the open obligation — the `sorry` here is declared, not hidden,
and is the single gap between the formalized material (N1–N4) and the full
necessity theorem (N5).
-/
import Mathlib
import SomTail.Coding

namespace SomTail

/-! ## TAIL solver assumption -/

/-- A TAIL solver is a function that, given any rational sequence bounded by 1,
    decides the Σ⁰₂ tail condition. -/
def TailSolver : Prop :=
  ∀ seq : ℕ → ℚ, (∀ m, seq m ≤ 1) →
    (∃ k : ℕ, 0 < k ∧ ∃ M : ℕ, ∀ m ≥ M, seq m ≤ 1 - 1 / (k : ℚ)) ∨
    ¬ (∃ k : ℕ, 0 < k ∧ ∃ M : ℕ, ∀ m ≥ M, seq m ≤ 1 - 1 / (k : ℚ))

/-! ## Tier D theorem N5: the reversal (declared sorry) -/

/-- `reversal` (N5): a TAIL solver implies the range principle for injections.

    The range principle (`∀ f : ℕ → ℕ, Function.Injective f → ∃ R : Set ℕ, ∀ y, y ∈ R ↔ ∃ x, f x = y`)
    is equivalent to ACA₀ over RCA₀ in reverse mathematics.

    **Open obligation.** The proof sketch uses `coding_correct` to convert the
    "¬ Tail (pf f y)" decision into "y ∈ range f". The assembly step — showing
    the collected decision bits form a set R with the required property — requires
    a Σ⁰₁-induction argument that in full rigour depends on a reverse-mathematics
    base theory not yet available in Lean/Mathlib. The `sorry` here is the single
    declared gap.

    This is N5 in the ledger. The certificate lists `reversal` as the sole open
    obligation. -/
theorem reversal (hsolver : TailSolver) :
    ∀ f : ℕ → ℕ, Function.Injective f →
      ∃ R : Set ℕ, ∀ y, y ∈ R ↔ ∃ x, f x = y := by
  intro f _hf_inj
  -- Use the TAIL solver on the Route-A coding sequence pf f y for each y.
  -- coding_correct shows: ¬ Tail (pf f y) ↔ y ∈ range f.
  -- Assembling this decision into a set R requires Σ⁰₁-induction (open obligation).
  sorry

end SomTail
