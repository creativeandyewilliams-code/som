import Mathlib
import SomTail.Coding
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

    **Open obligation.** The assembly step requires Σ⁰₁-induction in a
    reverse-mathematics base theory not yet available in Lean/Mathlib. -/
theorem reversal (hsolver : TailSolver) :
    ∀ f : ℕ → ℕ, Function.Injective f →
      ∃ R : Set ℕ, ∀ y, y ∈ R ↔ ∃ x, f x = y := by
  intro f _hf_inj
  sorry

end SomTail
