/-!
# SomTail.Witness — L1: First-order non-descent witness (Tier A)

Formalizes N1 from `som_necessity_program_v1.tex §9`.

State space, propagation, observation, proximity, and the two canonical witnesses
`xA` (latent mode A) and `xB` (latent mode B). The headline theorem `nondescent`
shows the two witnesses share a full observation history yet differ in tail status.

The tail predicate is given here in its elementary Σ⁰₂ form (an explicit
`∃ k ∃ M ∀ m` condition on the rational proximity sequence). Equivalence to the
`Filter.limsup` form is proved in `SomTail.Complexity`.
-/
import Mathlib

namespace SomTail

/-! ## Core definitions -/

/-- State space: latent mode (`false ↦ A`, `true ↦ B`) × infinite stream × index. -/
abbrev X := Bool × (ℕ → Bool) × ℕ

/-- Propagation: advance the index by one, leaving mode and stream unchanged. -/
def T : X → X | (θ, s, i) => (θ, s, i + 1)

/-- Observation: read the stream at the current index. -/
def o : X → Bool | (_, s, i) => s i

/-- Per-step predicate (identical to observation for this model). -/
def Phi : X → Bool | (_, s, i) => s i

/-- Latent proximity (rational-valued; avoids ℝ in Tier A).
    Mode A gives 0; mode B gives `1 - 1/(i+1)`. -/
def p : X → ℚ | (θ, _, i) => if θ then 1 - 1 / ((i : ℚ) + 1) else 0

/-- Finite observation history of length `n+1`: observations at steps 0..n. -/
def qFin (n : ℕ) (x : X) : List Bool :=
  (List.range (n + 1)).map fun k => o (T^[k] x)

/-- Full observation history: the infinite stream of observations. -/
def qInf (x : X) : ℕ → Bool := fun k => o (T^[k] x)

/-- Finite Phi-truncation: `true` iff Phi holds at every step 0..n. -/
def PhiTrunc (n : ℕ) (x : X) : Bool :=
  (List.range (n + 1)).all fun k => Phi (T^[k] x)

/-- Tail predicate (elementary Σ⁰₂ form).
    `Tail x` holds iff the proximity sequence is eventually bounded
    away from 1 by a positive rational gap `1/k`. -/
def Tail (x : X) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ M : ℕ, ∀ m ≥ M, p (T^[m] x) ≤ 1 - 1 / (k : ℚ)

/-- Canonical mode-A witness: latent mode false, stream all-true, index 0. -/
def xA : X := (false, fun _ => true, 0)

/-- Canonical mode-B witness: latent mode true, stream all-true, index 0. -/
def xB : X := (true, fun _ => true, 0)

/-! ## Supporting lemmas: iteration and proximity -/

@[simp]
lemma T_iter (m : ℕ) (θ : Bool) (s : ℕ → Bool) (i : ℕ) :
    T^[m] (θ, s, i) = (θ, s, i + m) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [T, ih]
    simp [Nat.add_succ]

lemma p_iter_xA (m : ℕ) : p (T^[m] xA) = 0 := by
  simp [xA, p]

lemma p_iter_xB (m : ℕ) : p (T^[m] xB) = 1 - 1 / ((m : ℚ) + 1) := by
  simp [xB, p]

lemma o_iter_xA (k : ℕ) : o (T^[k] xA) = true := by simp [xA, o]
lemma o_iter_xB (k : ℕ) : o (T^[k] xB) = true := by simp [xB, o]

/-! ## Theorem N1 (supporting): truncations factor through finite histories -/

/-- `trunc_factors`: `PhiTrunc` is a function of `qFin`, so equal finite histories
    imply equal finite truncations. -/
theorem trunc_factors (n : ℕ) (x y : X) (h : qFin n x = qFin n y) :
    PhiTrunc n x = PhiTrunc n y := by
  -- Key: Phi = o, so PhiTrunc n z = (qFin n z).all id for every z.
  suffices key : ∀ z : X, PhiTrunc n z = (qFin n z).all id by
    rw [key, key, h]
  intro z
  simp only [PhiTrunc, qFin, Phi, o]
  -- Now both sides are list-all of the same function; use all_map.
  induction (List.range (n + 1)) with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, ih]
    rfl

/-! ## Theorem N1 (supporting): the history tower strictly refines -/

/-- `tower_refines`: for every n, there exist x, y sharing their n-step
    history but differing at step n+1. -/
theorem tower_refines (n : ℕ) :
    ∃ x y : X, qFin n x = qFin n y ∧ qFin (n + 1) x ≠ qFin (n + 1) y := by
  -- Witness: x₀ has stream `decide (· ≤ n)`, x₁ has stream `fun _ => true`.
  refine ⟨(false, fun i => decide (i ≤ n), 0), (false, fun _ => true, 0), ?_, ?_⟩
  · -- Equal n-step histories: both observe `true` for steps 0..n.
    simp only [qFin, o, T_iter, zero_add]
    apply List.map_congr
    intro k hk
    simp only [List.mem_range] at hk
    simp [Nat.le_of_lt_succ hk]
  · -- Different (n+1)-step histories: x₀ has false at step n+1, x₁ has true.
    simp only [qFin, o, T_iter, zero_add, ne_eq]
    intro h
    -- false ∈ LHS (from step n+1 where decide (n+1 ≤ n) = false)
    have hmem_lhs : false ∈ (List.range (n + 2)).map (fun k => decide (k ≤ n)) := by
      apply List.mem_map.mpr
      exact ⟨n + 1, List.mem_range.mpr (Nat.lt_succ_self _), by
        simp [decide_eq_false_iff_not, Nat.not_succ_le_self]⟩
    -- false ∉ RHS (all entries are true)
    have hmem_rhs : false ∉ (List.range (n + 2)).map (fun _ => true) := by
      simp [List.mem_map]
    rw [h] at hmem_lhs
    exact hmem_rhs hmem_lhs

/-! ## Theorem N1 (core): shared full observation history -/

theorem hist_agree : qInf xA = qInf xB := by
  funext k
  simp [qInf, o_iter_xA, o_iter_xB]

/-! ## Theorem N1 (core): mode-A is in the tail -/

theorem tail_xA : Tail xA := by
  refine ⟨1, one_pos, 0, fun m _ => ?_⟩
  simp [p_iter_xA]

/-! ## Theorem N1 (core): mode-B is NOT in the tail -/

theorem tail_xB : ¬ Tail xB := by
  intro ⟨k, hk, M, hM⟩
  -- Apply the bound at m = max M k, which is ≥ M.
  have hbound := hM (max M k) (le_max_left M k)
  rw [p_iter_xB] at hbound
  -- Rational arithmetic: 1 - 1/(max M k + 1) ≤ 1 - 1/k implies k ≤ max M k, but also k+1 ≤ k.
  have hmk : k ≤ max M k := le_max_right M k
  have hkq : (0 : ℚ) < (k : ℚ) := Nat.cast_pos.mpr hk
  have hm1q : (0 : ℚ) < (max M k : ℚ) + 1 := by positivity
  -- From hbound: 1/k ≤ 1/(max M k + 1), i.e. max M k + 1 ≤ k. Contradicts hmk.
  have h_inv : 1 / (k : ℚ) ≤ 1 / ((max M k : ℚ) + 1) := by linarith
  have h_lt : (k : ℚ) < (max M k : ℚ) + 1 := by exact_mod_cast Nat.lt_succ_of_le hmk
  have h_anti : (max M k : ℚ) + 1 ≤ k := by
    rwa [div_le_div_iff hkq hm1q, one_mul, one_mul] at h_inv
  linarith

/-! ## Theorem N1 (headline): first-order non-descent -/

/-- `nondescent` (N1): the two canonical witnesses share their full observation
    history (`qInf xA = qInf xB`) yet are separated by the tail predicate
    (`Tail xA ↔ ¬ Tail xB`). This is the L1 deliverable. -/
theorem nondescent : qInf xA = qInf xB ∧ (Tail xA ↔ ¬ Tail xB) :=
  ⟨hist_agree, ⟨fun _ => tail_xB, fun _ => tail_xA⟩⟩

end SomTail
