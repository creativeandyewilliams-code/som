import Mathlib

/-!
# SomControlV11.Ledger.DebtRecurrence
Audit debt recurrence and divergence theorem.
  Debt(t+1) = max(0, Debt(t) + Demand(t) - Cap(t))
-/

namespace SomControlV11.Ledger

/-- One step of the debt recurrence. -/
def debtStep (debt demand cap : ℤ) : ℤ :=
  max 0 (debt + demand - cap)

/-- The debt sequence given demand and capacity functions (starting at 0). -/
def debtSeq (demand cap : ℕ → ℤ) : ℕ → ℤ
  | 0     => 0
  | n + 1 => debtStep (debtSeq demand cap n) (demand n) (cap n)

/-- Debt is non-negative throughout. -/
theorem debt_nonneg (demand cap : ℕ → ℤ) (n : ℕ) :
    0 ≤ debtSeq demand cap n := by
  induction n with
  | zero => simp [debtSeq]
  | succ n _ => simp [debtSeq, debtStep, le_max_left]

/-- Under persistent margin ε > 0, debt grows at least linearly. -/
theorem debt_diverges (demand cap : ℕ → ℤ) (ε : ℤ) (hε : 0 < ε)
    (hmargin : ∀ t, cap t + ε ≤ demand t) :
    ∀ n : ℕ, debtSeq demand cap n ≥ n * ε := by
  intro n
  induction n with
  | zero => simp [debtSeq]
  | succ n ih =>
    simp only [debtSeq, debtStep]
    have hstep : debtSeq demand cap n + demand n - cap n ≥ (n + 1) * ε := by
      have := hmargin n; linarith
    linarith [le_max_right 0 (debtSeq demand cap n + demand n - cap n)]

/-- Sufficient repair: if the quotient lies within capacity, debt does not grow. -/
theorem debt_stable_when_within_capacity (demand cap : ℕ → ℤ)
    (hwithin : ∀ t, demand t ≤ cap t) (n : ℕ) :
    debtSeq demand cap n = 0 := by
  induction n with
  | zero => simp [debtSeq]
  | succ n ih =>
    simp only [debtSeq, debtStep, ih]
    simp only [zero_add]
    exact max_eq_left (by linarith [hwithin n])

end SomControlV11.Ledger
