/-!
# SomTail.Complexity — L2: Σ⁰₂ form of the tail predicate (Tier B)

Formalizes N2 from `som_necessity_program_v1.tex §9`.

Proves the equivalence between the `Filter.limsup`-based tail predicate and the
elementary Σ⁰₂ (`∃ k ∃ M ∀ m`) form defined in `SomTail.Witness`. This is the
machine-checked statement that the tail sits at Σ⁰₂ in the arithmetical hierarchy.
-/
import Mathlib
import SomTail.Witness

namespace SomTail

open Filter Topology

/-! ## The limsup-based tail predicate -/

/-- `TailLimsup x`: the `Filter.limsup` form of the tail predicate.
    `x` is in the tail iff the real-valued proximity sequence has limsup strictly
    below 1. -/
def TailLimsup (x : X) : Prop :=
  Filter.limsup (fun m => (p (T^[m] x) : ℝ)) atTop < 1

/-! ## Tier B theorem: Σ⁰₂ characterisation (N2) -/

/-- `tail_iff_sigma02` (N2): the limsup-based tail predicate is equivalent to the
    explicit Σ⁰₂ condition on the rational proximity sequence.

    The backward direction (Σ⁰₂ → limsup < 1) is fully proved.
    The forward direction (limsup < 1 → Σ⁰₂) requires an Archimedean descent from
    the real bound to a rational `1 - 1/k`; marked `sorry` pending a clean
    mathlib path for this step. -/
theorem tail_iff_sigma02 (x : X) : TailLimsup x ↔ Tail x := by
  constructor
  · -- Forward: limsup < 1 → ∃ k > 0, ∃ M, ∀ m ≥ M, p (T^[m] x) ≤ 1 - 1/k.
    -- Archimedean descent from a real upper bound to a rational gap.
    intro hlt
    -- limsup < 1 means there exists c < 1 such that eventually p m ≤ c.
    rw [TailLimsup, limsup_lt_iff] at hlt
    obtain ⟨c, hc1, hc_bound⟩ := hlt
    rw [Filter.eventually_atTop] at hc_bound
    obtain ⟨M, hM⟩ := hc_bound
    -- By Archimedean, find k : ℕ with k > 0 and 1/k < 1 - c, i.e. c < 1 - 1/k.
    have hgap : (0 : ℝ) < 1 - c := by linarith
    obtain ⟨k, hk_pos, hk_bound⟩ := exists_nat_gt (1 / (1 - c))
    refine ⟨k, ?_, M, fun m hm => ?_⟩
    · exact_mod_cast Nat.pos_of_ne_zero (by intro h; simp [h] at hk_bound; linarith)
    · -- p (T^[m] x) ≤ c in ℝ, and c ≤ 1 - 1/k, so p ≤ 1 - 1/k in ℚ.
      have hpm_le : (p (T^[m] x) : ℝ) ≤ c := hM m hm
      have hk_q : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by intro h; simp [h] at hk_bound; linarith)
      have hcinv : c ≤ 1 - 1 / (k : ℝ) := by
        rw [div_lt_iff (by linarith : (0:ℝ) < 1 - c)] at hk_bound
        linarith [mul_comm (k : ℝ) (1 - c)]
      have hle_real : (p (T^[m] x) : ℝ) ≤ 1 - 1 / (k : ℝ) := le_trans hpm_le hcinv
      -- Transfer the inequality from ℝ back to ℚ.
      have : (p (T^[m] x) : ℝ) ≤ ((1 - 1 / (k : ℚ)) : ℚ) := by
        push_cast at hle_real ⊢
        linarith
      exact_mod_cast Rat.cast_le.mp (by exact_mod_cast this)
  · -- Backward: Σ⁰₂ → limsup < 1.
    intro ⟨k, hk, M, hM⟩
    -- The sequence is eventually ≤ 1 - 1/k < 1; hence limsup ≤ 1 - 1/k < 1.
    have hkq : (0 : ℚ) < k := Nat.cast_pos.mpr hk
    have hbound : (1 : ℚ) - 1 / k < 1 := by
      have : (0 : ℚ) < 1 / k := div_pos one_pos hkq
      linarith
    have hbound_R : (1 : ℝ) - 1 / k < 1 := by exact_mod_cast hbound
    apply lt_of_le_of_lt _ hbound_R
    apply Filter.limsup_le_of_le
    · exact isBoundedUnder_of (f := atTop) ⟨(1 - 1 / (k : ℝ)), by
        apply Filter.eventually_atTop.mpr
        exact ⟨M, fun m hm => by exact_mod_cast hM m hm⟩⟩
    · apply Filter.eventually_atTop.mpr
      exact ⟨M, fun m hm => by exact_mod_cast hM m hm⟩

end SomTail
