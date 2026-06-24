import Mathlib
import SomTail.Witness
/-!
# SomTail.Coding — L4: Route-A coding reduction (Tier D)

Formalizes N4 from `som_necessity_program_v1.tex §9`.

Defines the Route-A proximity sequence `pf f y` associated to a function `f : ℕ → ℕ`
and target `y`. The key theorem `coding_correct` shows that the tail condition fails
(no eventual rational gap below 1) precisely when `y` is in the range of `f`.
This is the heart of the coding reduction.
-/

namespace SomTail

open Classical in
/-- `pf f y m`: the proximity value at step `m` for target `y` under `f`.
    The guard `∃ x ≤ m, f x = y` is a bounded search (Δ⁰₁ with oracle).
    Once found it stays true, so pf eventually equals `1 - 1/(m+1)` when `y ∈ range f`. -/
noncomputable def pf (f : ℕ → ℕ) (y : ℕ) : ℕ → ℚ :=
  fun m => if (∃ x ≤ m, f x = y) then 1 - 1 / ((m : ℚ) + 1) else 0

/-! ## Auxiliary lemmas -/

lemma pf_pos_iff (f : ℕ → ℕ) (y m : ℕ) :
    pf f y m > 0 ↔ ∃ x ≤ m, f x = y := by
  simp only [pf]
  split_ifs with h
  · constructor
    · intro _; exact h
    · intro _
      have hpos : (0 : ℚ) < (m : ℚ) + 1 := by positivity
      have : 1 / ((m : ℚ) + 1) < 1 := by
        rw [div_lt_one hpos]; linarith
      linarith
  · simp [h]

lemma pf_eq_of_found (f : ℕ → ℕ) (y m : ℕ) (h : ∃ x ≤ m, f x = y) :
    pf f y m = 1 - 1 / ((m : ℚ) + 1) := by
  simp only [pf, h, if_true]

lemma found_mono (f : ℕ → ℕ) (y : ℕ) (x₀ : ℕ) (hx₀ : f x₀ = y) :
    ∀ m ≥ x₀, ∃ x ≤ m, f x = y :=
  fun m hm => ⟨x₀, hm, hx₀⟩

/-! ## Tier D theorem: coding correctness (N4) -/

/-- `coding_correct` (N4): the tail's failure mode (no eventual rational gap below 1)
    holds if and only if `y` is in the range of `f`. -/
theorem coding_correct (f : ℕ → ℕ) (y : ℕ) :
    (¬ ∃ k : ℕ, 0 < k ∧ ∃ M : ℕ, ∀ m ≥ M, pf f y m ≤ 1 - 1 / (k : ℚ))
      ↔ (∃ x, f x = y) := by
  constructor
  · intro hnt
    push_neg at hnt
    have h1 : ∀ M : ℕ, ∃ m ≥ M, pf f y m > 1 - 1 / (1 : ℚ) := hnt 1 one_pos
    simp only [Nat.cast_one, div_one, sub_self] at h1
    obtain ⟨m, _, hm_pos⟩ := h1 0
    rw [pf_pos_iff] at hm_pos
    exact ⟨hm_pos.choose, hm_pos.choose_spec.2⟩
  · intro ⟨x₀, hx₀⟩ ⟨k, hk, M, hM⟩
    set m := max (max M x₀) k with hm_def
    have hm_M : m ≥ M := Nat.le_trans (Nat.le_max_left M x₀) (Nat.le_max_left _ k)
    have hm_x₀ : m ≥ x₀ := Nat.le_trans (Nat.le_max_right M x₀) (Nat.le_max_left _ k)
    have hm_k : m ≥ k := Nat.le_max_right _ k
    have hpf : pf f y m = 1 - 1 / ((m : ℚ) + 1) :=
      pf_eq_of_found f y m (found_mono f y x₀ hx₀ m hm_x₀)
    have hbound := hM m hm_M
    rw [hpf] at hbound
    have hkq : (0 : ℚ) < (k : ℚ) := Nat.cast_pos.mpr hk
    have hm1q : (0 : ℚ) < (m : ℚ) + 1 := by positivity
    have hmkq : (k : ℚ) ≤ (m : ℚ) := Nat.cast_le.mpr hm_k
    have h_lt : (1 : ℚ) / ((m : ℚ) + 1) < 1 / (k : ℚ) := by
      rw [div_lt_div_iff hm1q hkq, one_mul, one_mul]
      linarith
    linarith

end SomTail
