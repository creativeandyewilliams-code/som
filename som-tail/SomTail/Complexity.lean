import Mathlib
import SomTail.Witness
/-!
# SomTail.Complexity — L2: Σ⁰₂ form of the tail predicate (Tier B)

Formalizes N2 from `som_necessity_program_v1.tex §9`.

Proves the equivalence between the `Filter.limsup`-based tail predicate and the
elementary Σ⁰₂ (`∃ k ∃ M ∀ m`) form defined in `SomTail.Witness`. This is the
machine-checked statement that the tail sits at Σ⁰₂ in the arithmetical hierarchy.
-/

namespace SomTail

open Filter Topology

/-! ## The limsup-based tail predicate -/

/-- `TailLimsup x`: the `Filter.limsup` form of the tail predicate. -/
def TailLimsup (x : X) : Prop :=
  Filter.limsup (fun m => (p (T^[m] x) : ℝ)) atTop < 1

/-! ## Bounds on p -/

lemma p_le_one (x : X) : p x ≤ 1 := by
  unfold p
  split_ifs with h
  · have hpos : (0 : ℚ) < (x.2.2 : ℚ) + 1 := by positivity
    linarith [div_pos one_pos hpos, div_le_one hpos |>.mpr (by linarith)]
  · norm_num

/-! ## Tier B theorem: Σ⁰₂ characterisation (N2) -/

/-- `tail_iff_sigma02` (N2): `TailLimsup x ↔ Tail x`. -/
theorem tail_iff_sigma02 (x : X) : TailLimsup x ↔ Tail x := by
  constructor
  · intro hlt
    unfold TailLimsup at hlt
    have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun m => (p (T^[m] x) : ℝ)) :=
      ⟨1, Filter.eventually_of_forall (fun m => by exact_mod_cast p_le_one _)⟩
    rw [Filter.limsup_lt_iff hbdd] at hlt
    obtain ⟨c, hc1, hc_ev⟩ := hlt
    rw [Filter.eventually_atTop] at hc_ev
    obtain ⟨M, hM⟩ := hc_ev
    have hgap : (0 : ℝ) < 1 - c := by linarith
    obtain ⟨k, hk_bound⟩ := exists_nat_gt (1 / (1 - c))
    have hk_pos : 0 < k := by
      by_contra h
      push_neg at h
      interval_cases k
      simp at hk_bound
      linarith [div_pos one_pos hgap]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk_pos
    refine ⟨k, hk_pos, M, fun m hm => ?_⟩
    have hcq : c ≤ 1 - 1 / (k : ℝ) := by
      rw [div_lt_iff hgap] at hk_bound
      rw [le_sub_iff_add_le, div_add_eq (ne_of_gt hkR), div_le_one hkR]
      linarith
    have hle_R : (p (T^[m] x) : ℝ) ≤ 1 - 1 / (k : ℝ) := le_trans (hM m hm) hcq
    have hcast : ((1 - 1 / (k : ℚ)) : ℝ) = 1 - 1 / (k : ℝ) := by push_cast; ring
    exact_mod_cast hcast ▸ (Rat.cast_le.mp (by linarith [hle_R, hcast.symm ▸ hle_R]))
  · intro ⟨k, hk, M, hM⟩
    have hkq : (0 : ℚ) < k := Nat.cast_pos.mpr hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkq
    have hbound_R : (1 : ℝ) - 1 / k < 1 := by linarith [div_pos one_pos hkR]
    have hev : ∀ᶠ m in atTop, (p (T^[m] x) : ℝ) ≤ 1 - 1 / (k : ℝ) := by
      apply Filter.eventually_atTop.mpr
      exact ⟨M, fun m hm => by exact_mod_cast hM m hm⟩
    calc Filter.limsup (fun m => (p (T^[m] x) : ℝ)) atTop
        ≤ 1 - 1 / (k : ℝ) := Filter.limsup_le_of_le ⟨_, hev⟩ hev
      _ < 1 := hbound_R

end SomTail
