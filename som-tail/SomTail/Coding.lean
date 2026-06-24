/-!
# SomTail.Coding — L4: Route-A coding reduction (Tier D)

Formalizes N4 from `som_necessity_program_v1.tex §9`.

Defines the Route-A proximity sequence `pf f y` associated to an injection `f`
and target `y`. The key theorem `coding_correct` shows that the tail condition
fails (i.e. limsup = 1) precisely when `y` is in the range of `f`. This is the
heart of the coding reduction and the highest-value certificate after Tier A.
-/
import Mathlib
import SomTail.Witness

namespace SomTail

/-! ## Route-A coding -/

/-- `pf f y m`: the proximity value at step `m` for target `y` under injection `f`.
    The guard `∃ x ≤ m, f x = y` is a bounded (Δ⁰₁) search. -/
def pf (f : ℕ → ℕ) (y : ℕ) : ℕ → ℚ :=
  fun m => if (∃ x ≤ m, f x = y) then 1 - 1 / ((m : ℚ) + 1) else 0

/-- Once `y` enters the range of `f`, it stays entered. -/
lemma pf_eventually_pos (f : ℕ → ℕ) (y : ℕ) (hfy : ∃ x, f x = y) :
    ∃ M : ℕ, ∀ m ≥ M, (∃ x ≤ m, f x = y) := by
  obtain ⟨x, hx⟩ := hfy
  exact ⟨x, fun m hm => ⟨x, hm, hx⟩⟩

/-- If `y ∉ range f` then `pf f y m = 0` for all `m`. -/
lemma pf_zero_of_not_range (f : ℕ → ℕ) (y : ℕ) (hfy : ¬∃ x, f x = y) (m : ℕ) :
    pf f y m = 0 := by
  simp only [pf]
  split_ifs with h
  · obtain ⟨x, _, hx⟩ := h; exact absurd ⟨x, hx⟩ hfy
  · rfl

/-! ## Tier D theorem: coding correctness (N4) -/

/-- `coding_correct` (N4): the tail's failure mode (no eventual rational gap below 1)
    holds if and only if `y` is in the range of `f`.

    Direction (→): if `¬ Tail (pf f y)`, then for every `k > 0` and `M`, some
    step `m ≥ M` has `pf f y m > 1 - 1/k`. Since `pf f y m > 0` requires
    `∃ x ≤ m, f x = y`, we get `y ∈ range f`.

    Direction (←): if `y ∈ range f`, then from some index on, `pf f y m = 1 - 1/(m+1) → 1`,
    which rises past every `1 - 1/k`, so no eventual gap exists. -/
theorem coding_correct (f : ℕ → ℕ) (y : ℕ) :
    (¬ ∃ k : ℕ, 0 < k ∧ ∃ M : ℕ, ∀ m ≥ M, pf f y m ≤ 1 - 1 / (k : ℚ))
      ↔ (∃ x, f x = y) := by
  constructor
  · -- (→): negation of tail → y in range of f.
    intro hnt
    push_neg at hnt
    -- For k = 1, there is no M with ∀ m ≥ M, pf ≤ 0. So pf takes positive values
    -- unboundedly. pf f y m > 0 requires a witness x ≤ m with f x = y.
    have h1 : ∀ M : ℕ, ∃ m ≥ M, pf f y m > 1 - 1 / (1 : ℚ) := hnt 1 one_pos
    -- 1 - 1/1 = 0, so pf f y m > 0 for unboundedly many m.
    simp only [Nat.cast_one, div_one, sub_self] at h1
    obtain ⟨m, _, hm_pos⟩ := h1 0
    simp only [pf] at hm_pos
    split_ifs at hm_pos with h
    · exact ⟨(h.choose), h.choose_spec.2⟩
    · linarith
  · -- (←): y in range of f → negation of tail.
    intro ⟨x₀, hx₀⟩ ⟨k, hk, M, hM⟩
    -- From M' = max M x₀ onward, pf f y m = 1 - 1/(m+1).
    have hfound : ∀ m ≥ x₀, ∃ x ≤ m, f x = y := fun m hm => ⟨x₀, hm, hx₀⟩
    -- At m = max (max M x₀) k, both the M bound and the x₀ bound hold,
    -- and m+1 > k so 1 - 1/(m+1) > 1 - 1/k, contradicting hM.
    set m := max (max M x₀) k with hm_def
    have hm_M : m ≥ M := le_trans (le_max_left M x₀) (le_max_left _ k)
    have hm_x₀ : m ≥ x₀ := le_trans (le_max_right M x₀) (le_max_left _ k)
    have hm_k : m ≥ k := le_max_right _ k
    have hpf : pf f y m = 1 - 1 / ((m : ℚ) + 1) := by
      simp only [pf]
      have := hfound m hm_x₀
      simp [this]
    have hbound := hM m hm_M
    rw [hpf] at hbound
    have hkq : (0 : ℚ) < k := Nat.cast_pos.mpr hk
    have hm1q : (0 : ℚ) < (m : ℚ) + 1 := by positivity
    have hmkq : (k : ℚ) ≤ (m : ℚ) := Nat.cast_le.mpr hm_k
    have h_contra : (1 : ℚ) - 1 / (k : ℚ) < 1 - 1 / ((m : ℚ) + 1) := by
      have : 1 / ((m : ℚ) + 1) < 1 / (k : ℚ) := by
        rw [div_lt_div_iff hm1q hkq, one_mul, one_mul]
        linarith
      linarith
    linarith

end SomTail
