import Mathlib
import SomControlV11.Core.Factorization

/-!
# SomControlV11.Temporal.RichWitness
V11 rich temporal non-descent witness.
Uses the dyadic threshold 1 - 1/2^k as specified in V11 §4.
-/

namespace SomControlV11.Temporal

open SomControlV11.Core

/-! ## State space -/

abbrev X := Bool × (ℕ → Bool) × ℕ

def T : X → X | (θ, s, i) => (θ, s, i + 1)
def o : X → Bool | (_, s, i) => s i
def a : X → ℚ | (θ, _, i) => if θ then 1 - 1 / ((i : ℚ) + 1) else 0

/-! ## V11 dyadic threshold predicates -/

/-- Below(x): proximity eventually stays ≤ 1 - 1/2^k for some k > 0. -/
def Below (x : X) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ M : ℕ, ∀ m ≥ M, a (T^[m] x) ≤ 1 - 1 / (2 : ℚ)^k

/-- AtOne(x): proximity exceeds 1 - 1/2^k unboundedly often for every k > 0. -/
def AtOne (x : X) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ M : ℕ, ∃ m ≥ M, a (T^[m] x) > 1 - 1 / (2 : ℚ)^k

/-! ## Observation histories -/

def qFin (n : ℕ) (x : X) : List Bool :=
  (List.range (n + 1)).map fun k => o (T^[k] x)

def qInf (x : X) : ℕ → Bool := fun k => o (T^[k] x)

/-- Finite monitor: all observations up to stage n are true. -/
def PhiMon (n : ℕ) (x : X) : Bool := (qFin n x).all id

/-! ## Canonical witnesses -/

def xA : X := (false, fun _ => true, 0)
def xB : X := (true, fun _ => true, 0)

/-! ## Iteration -/

@[simp]
lemma T_iter (m : ℕ) (θ : Bool) (s : ℕ → Bool) (i : ℕ) :
    T^[m] (θ, s, i) = (θ, s, i + m) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [T, ih]
    exact Prod.ext rfl (Prod.ext rfl (by omega))

lemma a_iter_xA (m : ℕ) : a (T^[m] xA) = 0 := by simp [xA, a]
lemma a_iter_xB (m : ℕ) : a (T^[m] xB) = 1 - 1 / ((m : ℚ) + 1) := by simp [xB, a]
lemma o_iter_xA (k : ℕ) : o (T^[k] xA) = true := by simp [xA, o]
lemma o_iter_xB (k : ℕ) : o (T^[k] xB) = true := by simp [xB, o]

/-! ## Monitor decoder -/

/-- The stage-n monitor factors through qFin: equal finite histories ⇒ equal monitor output. -/
theorem monitor_decoder (n : ℕ) (x y : X) (h : qFin n x = qFin n y) :
    PhiMon n x = PhiMon n y := by
  simp [PhiMon, h]

/-! ## Strict history refinement -/

theorem history_strictly_refines (n : ℕ) :
    ∃ x y : X, qFin n x = qFin n y ∧ qFin (n + 1) x ≠ qFin (n + 1) y := by
  refine ⟨(false, fun i => decide (i ≤ n), 0),
          (false, fun _ => true, 0), ?_, ?_⟩
  · simp only [qFin, o, T_iter, zero_add]
    apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    simp [Nat.le_of_lt_succ hk]
  · simp only [qFin, o, T_iter, zero_add, ne_eq]
    intro h
    have hmem_lhs : false ∈ (List.range (n + 2)).map (fun k => decide (k ≤ n)) := by
      apply List.mem_map.mpr
      exact ⟨n + 1, List.mem_range.mpr (Nat.lt_succ_self _), by
        simp [decide_eq_false_iff_not, Nat.not_succ_le_self]⟩
    have hmem_rhs : false ∉ (List.range (n + 2)).map (fun _ => true) := by
      simp [List.mem_map]
    exact hmem_rhs (h ▸ hmem_lhs)

/-! ## Core V11 theorems -/

theorem xA_Below : Below xA :=
  ⟨1, one_pos, 0, fun m _ => by rw [a_iter_xA]; norm_num⟩

theorem xB_AtOne : AtOne xB := by
  intro k hk M
  refine ⟨max M (2^k), le_max_left _ _, ?_⟩
  rw [a_iter_xB, gt_iff_lt, sub_lt_sub_iff_left]
  have h2k : (0 : ℚ) < (2 : ℚ)^k := by positivity
  have hm1 : (0 : ℚ) < (max M (2^k) : ℚ) + 1 := by positivity
  rw [div_lt_div_iff hm1 h2k, one_mul, one_mul]
  have : (2^k : ℚ) ≤ (max M (2^k) : ℚ) := by
    exact_mod_cast Nat.le_max_right M (2^k)
  linarith

theorem xB_not_Below : ¬ Below xB := by
  intro ⟨k, hk, M, hM⟩
  obtain ⟨m, hm_ge, hm_gt⟩ := xB_AtOne k hk M
  exact absurd (hM m hm_ge) (not_le.mpr hm_gt)

theorem hist_agree : qInf xA = qInf xB := by
  funext k; simp [qInf, o_iter_xA, o_iter_xB]

theorem finHist_agree (n : ℕ) : qFin n xA = qFin n xB := by
  simp [qFin, o_iter_xA, o_iter_xB]

/-- V11 rich temporal non-descent: equal full history, separated orbit target. -/
theorem rich_nondescent :
    qInf xA = qInf xB ∧ Below xA ∧ ¬ Below xB :=
  ⟨hist_agree, xA_Below, xB_not_Below⟩

/-- The orbit target (Below) does not factor through the full observation history. -/
theorem orbit_target_no_factor :
    ¬ ∃ d : (ℕ → Bool) → Prop, ∀ x : X, Below x ↔ d (qInf x) := by
  rintro ⟨d, hd⟩
  have hA : d (qInf xA) := (hd xA).mp xA_Below
  rw [hist_agree] at hA
  exact xB_not_Below ((hd xB).mpr hA)

end SomControlV11.Temporal
