import Mathlib

/-!
# SomControlV11.ReverseMath.CodingReduction
V11 coding reduction, Level A (ambient Lean metatheory).

Constructs the proximity array a_f and proves:
  y ∈ ran(f) → AtOne(a_f, y)  [approaches 1 with dyadic threshold]
  y ∉ ran(f) → Below(a_f, y)   [bounded below 1 with dyadic threshold]

This is a machine-checked formalization of the V11 construction in ordinary Lean
mathematics. It is NOT a proof over RCA₀ (that requires Level B: a formalized
RCA₀ metatheory, which is a separate pending project).
-/

namespace SomControlV11.ReverseMath

open Classical in
/-- V11 coded proximity array.
    a_f(y, m) = 1 - 1/(m+1) if ∃ x ≤ m, f x = y; else 0. -/
noncomputable def a_f (f : ℕ → ℕ) (y m : ℕ) : ℚ :=
  if (∃ x ≤ m, f x = y) then 1 - 1 / ((m : ℚ) + 1) else 0

lemma a_f_found (f : ℕ → ℕ) (y m : ℕ) (h : ∃ x ≤ m, f x = y) :
    a_f f y m = 1 - 1 / ((m : ℚ) + 1) := by
  simp [a_f, h]

lemma a_f_notfound (f : ℕ → ℕ) (y m : ℕ) (h : ¬ ∃ x ≤ m, f x = y) :
    a_f f y m = 0 := by
  simp [a_f, h]

/-! ## V11 coding theorems with dyadic threshold -/

/-- y ∈ ran(f) implies a_f(y,·) satisfies AtOne with dyadic threshold.
    Uses V11 choice m ≥ max(M, x₀, 2^k). -/
theorem in_range_atOne (f : ℕ → ℕ) (y : ℕ) (hy : ∃ x₀, f x₀ = y) :
    ∀ k : ℕ, 0 < k → ∀ M : ℕ,
      ∃ m ≥ M, a_f f y m > 1 - 1 / (2 : ℚ)^k := by
  intro k _ M
  obtain ⟨x₀, hx₀⟩ := hy
  let m := max (max M x₀) (2^k)
  refine ⟨m, Nat.le_trans (Nat.le_max_left M x₀) (Nat.le_max_left _ _), ?_⟩
  have hfound : ∃ x ≤ m, f x = y :=
    ⟨x₀, Nat.le_trans (Nat.le_max_right M x₀) (Nat.le_max_left _ _), hx₀⟩
  rw [a_f_found _ _ _ hfound, gt_iff_lt, sub_lt_sub_iff_left]
  have h2k : (0 : ℚ) < (2 : ℚ)^k := by positivity
  have hm1 : (0 : ℚ) < (m : ℚ) + 1 := by positivity
  rw [div_lt_div_iff hm1 h2k, one_mul, one_mul]
  have : (2^k : ℚ) ≤ (m : ℚ) := by
    exact_mod_cast Nat.le_max_right (max M x₀) (2^k)
  linarith

/-- y ∉ ran(f) implies a_f(y,·) satisfies Below with dyadic threshold. -/
theorem not_in_range_below (f : ℕ → ℕ) (y : ℕ) (hy : ¬ ∃ x₀, f x₀ = y) :
    ∃ k : ℕ, 0 < k ∧ ∃ M : ℕ, ∀ m ≥ M, a_f f y m ≤ 1 - 1 / (2 : ℚ)^k := by
  refine ⟨1, one_pos, 0, fun m _ => ?_⟩
  have hnotfound : ¬ ∃ x ≤ m, f x = y := fun ⟨x, _, hx⟩ => hy ⟨x, hx⟩
  rw [a_f_notfound _ _ _ hnotfound]
  norm_num

/-- V11 coding correctness: y ∈ ran(f) ↔ ¬Below(a_f, y). -/
theorem coding_correct (f : ℕ → ℕ) (y : ℕ) :
    (∃ x, f x = y) ↔
    ¬ ∃ k : ℕ, 0 < k ∧ ∃ M : ℕ, ∀ m ≥ M, a_f f y m ≤ 1 - 1 / (2 : ℚ)^k := by
  constructor
  · intro hy ⟨k, hk, M, hM⟩
    obtain ⟨m, hm_ge, hm_gt⟩ := in_range_atOne f y hy k hk M
    exact absurd (hM m hm_ge) (not_le.mpr hm_gt)
  · intro hnotbelow
    by_contra hy
    exact hnotbelow (not_in_range_below f y hy)

end SomControlV11.ReverseMath
