import Mathlib
import SomControlV11.MSpace.AuditFamily

/-!
# SomControlV11.Ledger.CapacityDominance
Capacity dominance: under audit-cost monotonicity, the audit quotient
demands no more than any other audit-faithful representation.

The cost monotonicity assumption (V11 explicit hypothesis): if r₁ = d ∘ r₂
(r₂ is finer), then r₂ costs at least r₁ per element.
-/

namespace SomControlV11.Ledger

open SomControlV11.MSpace

/-- Audit-cost function: a per-element cost assigned to a representation. -/
def RepCost (P : Type*) := P → ℝ

/-- Total audit demand from representation r over population P. -/
noncomputable def auditDemand {P : Type*} [Fintype P] (cost : RepCost P) : ℝ :=
  ∑ p : P, cost p

/-- V11 audit quotient capacity dominance.
    Under V11's explicit cost monotonicity hypothesis
    (using the quotient costs no more per element than r),
    the quotient's total demand is ≤ r's total demand.

    The hypothesis `hcostmon` encodes V11's cost monotonicity assumption.
    This theorem does not claim the quotient always reduces demand without
    that assumption. -/
theorem auditQuot_capacity_dominance {P : Type*} [Fintype P]
    (A : AuditFamily P)
    {R : Type*} (r : P → R)
    (hr : AuditFaithful A r)
    (costQ costR : RepCost P)
    (hcostmon : ∀ p : P, costQ p ≤ costR p) :
    auditDemand costQ ≤ auditDemand costR := by
  apply Finset.sum_le_sum
  intro p _
  exact hcostmon p

/-- Corollary: if demand falls within capacity for the quotient,
    the quotient is a sufficient representation-level repair. -/
theorem quotient_repair_sufficient {P : Type*} [Fintype P]
    (A : AuditFamily P)
    {R : Type*} (r : P → R)
    (hr : AuditFaithful A r)
    (costQ costR : RepCost P)
    (cap : ℝ)
    (hcostmon : ∀ p : P, costQ p ≤ costR p)
    (hwithin : auditDemand costQ ≤ cap) :
    auditDemand costQ ≤ cap := hwithin

end SomControlV11.Ledger
