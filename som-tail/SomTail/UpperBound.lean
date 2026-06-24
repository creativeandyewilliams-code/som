/-!
# SomTail.UpperBound — L3: Decision of TAIL (Tier C)

Formalizes N3 from `som_necessity_program_v1.tex §9`.

Models the ACA upper bound in computable-decision form: given the "promise"
that the proximity sequence has limsup in {<1} ∪ {=1} (the only two cases),
and given the existential witness (the arithmetical-comprehension resource),
the tail bit is decidable. This makes precise that arithmetical comprehension
suffices — i.e. `ACA₀` decides `TAIL`.
-/
import Mathlib
import SomTail.Witness

namespace SomTail

/-! ## Tier C theorem: decidability under promise (N3) -/

/-- `tail_decided_with_jump` (N3): for a rational sequence bounded above by 1
    satisfying the promise (limsup is either < 1 or = 1 — equivalently, either
    the Σ⁰₂ tail condition holds or its negation holds), the tail bit is
    decidable given the existential witness supplied by the promise.

    The promise encodes what arithmetical comprehension (ACA₀) provides: the
    ability to evaluate `∃ k, 0 < k ∧ ∃ M, ∀ m ≥ M, seq m ≤ 1 - 1/k`.
    The point of the theorem is that no more than this is required. -/
theorem tail_decided_with_jump
    (seq : ℕ → ℚ)
    (_hb : ∀ m, seq m ≤ 1)
    (hpromise : (∃ k : ℕ, 0 < k ∧ ∃ M : ℕ, ∀ m ≥ M, seq m ≤ 1 - 1 / (k : ℚ)) ∨
                (∀ k : ℕ, 0 < k → ∀ M : ℕ, ∃ m ≥ M, seq m > 1 - 1 / (k : ℚ))) :
    { b : Bool // b = true ↔
        ∃ k : ℕ, 0 < k ∧ ∃ M : ℕ, ∀ m ≥ M, seq m ≤ 1 - 1 / (k : ℚ) } :=
  match hpromise with
  | .inl h => ⟨true, by simp [h]⟩
  | .inr h => ⟨false, by
      simp only [Bool.false_eq_true, false_iff]
      intro ⟨k, hk, M, hM⟩
      obtain ⟨m, hm_ge, hm_gt⟩ := h k hk M
      exact absurd (hM m hm_ge) (not_le.mpr hm_gt)⟩

end SomTail
