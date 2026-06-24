import SomControlV11.Core.Factorization
import SomControlV11.Core.TypedRecord
import SomControlV11.Core.DecisionPartitions
import SomControlV11.Temporal.RichWitness
import SomControlV11.Diagnostic.Binding
import SomControlV11.ReverseMath.CodingReduction
import SomControlV11.MSpace.AuditFamily
import SomControlV11.MSpace.AuditQuotient
import SomControlV11.Ledger.DebtRecurrence
import SomControlV11.Ledger.CapacityDominance
import SomControlV11.Derivation.NoveltySeparation
import SomControlV11.Derivation.AuditEquivalentNecessity
import SomControlV11.PSpace.GenericAspectAudit

/-!
# SomControlV11.Release.V11Claims
V11 formal companion release target — verified declarations only.

Build command:
  lake build SomControlV11.Release.V11Claims

## Verified (no proof holes)
- Fiber criterion and paired certificate soundness                [Core.Factorization]
- Typed diagnostic status (descent/nondescent/incomplete)        [Core.TypedRecord]
- Kernel equivalence and coarsest decision partition             [Core.DecisionPartitions]
- Rich temporal non-descent with V11 dyadic threshold 1-2^(-k)  [Temporal.RichWitness]
- Monitor decoder (finite history => monitor output)             [Temporal.RichWitness]
- Strict history refinement                                      [Temporal.RichWitness]
- Orbit target does not factor through full observation history  [Temporal.RichWitness]
- Binding-sensitive diagnostic non-factorization                 [Diagnostic.Binding]
- V11 coding reduction Level A (ambient Lean metatheory)         [ReverseMath.CodingReduction]
- Audit equivalence setoid and coarsest audit quotient           [MSpace.AuditFamily]
- Surjectivity of audit quotient map                            [MSpace.AuditQuotient]
- Debt recurrence, divergence, and stable repair condition       [Ledger.DebtRecurrence]
- Capacity dominance under cost monotonicity hypothesis          [Ledger.CapacityDominance]
- Novelty separation (obs-history indistinguishable pair)        [Derivation.NoveltySeparation]
- Audit-equivalent necessity (Below not obs-computable)          [Derivation.AuditEquivalentNecessity]
- No Bool-valued observation classifier for Below                [Derivation.AuditEquivalentNecessity]
- No finite-history classifier for any depth n                   [Derivation.AuditEquivalentNecessity]
- Generic aspect-audit separation (auditor-distinct => quot-distinct) [PSpace.GenericAspectAudit]

## Pending (proof holes present — excluded from release graph)
- R³ edge-separated embedding (moment curve / Vandermonde)       [Visual.R3Embedding]
- K₅ lower-bound obstruction (planarity)                        [Visual.PlanarityObstruction]
- UGapTail <-> ACA0 (Level B: requires formalized RCA0 metatheory) [ReverseMath.ACA0Equivalence]
- Quotient topology / metrizability for P-space audit quotient   [PSpace level B]

## Not formalized (empirical bridge)
- Corpus forecasts, human performance claims, repository ledger
  These are preregistered empirical hypotheses, not theorem certificates.

## Axioms
This release relies on the standard Lean/Mathlib axiom set:
  Classical.choice, propext, Quot.sound, funext.
No additional trusted axioms.
-/

namespace SomControlV11.Release

-- Core factorization
alias fiber_criterion              := SomControlV11.Core.fiber_criterion
alias no_factor_of_paired          := SomControlV11.Core.no_factor_of_paired
alias descent_sound                := SomControlV11.Core.descent_sound
alias nondescent_sound             := SomControlV11.Core.nondescent_sound
alias refines_iff_factors          := SomControlV11.Core.refines_iff_factors
alias factorization_refines_kernel := SomControlV11.Core.factorization_refines_kernel

-- Temporal
alias xA_Below                 := SomControlV11.Temporal.xA_Below
alias xB_AtOne                 := SomControlV11.Temporal.xB_AtOne
alias xB_not_Below             := SomControlV11.Temporal.xB_not_Below
alias hist_agree               := SomControlV11.Temporal.hist_agree
alias rich_nondescent          := SomControlV11.Temporal.rich_nondescent
alias orbit_target_no_factor   := SomControlV11.Temporal.orbit_target_no_factor
alias monitor_decoder          := SomControlV11.Temporal.monitor_decoder
alias history_strictly_refines := SomControlV11.Temporal.history_strictly_refines

-- Diagnostic
alias binding_nonfactorization := SomControlV11.Diagnostic.binding_nonfactorization

-- Reverse mathematics (Level A)
alias in_range_atOne     := SomControlV11.ReverseMath.in_range_atOne
alias not_in_range_below := SomControlV11.ReverseMath.not_in_range_below
alias coding_correct     := SomControlV11.ReverseMath.coding_correct

-- MSpace audit quotient
alias auditQuot_faithful      := SomControlV11.MSpace.auditQuot_faithful
alias coarsest_audit_faithful := SomControlV11.MSpace.coarsest_audit_faithful
alias auditQuot_is_coarsest   := SomControlV11.MSpace.auditQuot_is_coarsest
alias auditQuot_surjective    := SomControlV11.MSpace.auditQuot_surjective

-- Ledger
alias debt_nonneg                      := SomControlV11.Ledger.debt_nonneg
alias debt_diverges                    := SomControlV11.Ledger.debt_diverges
alias debt_stable_when_within_capacity := SomControlV11.Ledger.debt_stable_when_within_capacity
alias auditQuot_capacity_dominance     := SomControlV11.Ledger.auditQuot_capacity_dominance

-- Derivation
alias novelty_separation           := SomControlV11.Derivation.novelty_separation
alias no_obs_separator             := SomControlV11.Derivation.no_obs_separator
alias audit_equivalent_necessity   := SomControlV11.Derivation.audit_equivalent_necessity
alias no_bool_classifier           := SomControlV11.Derivation.no_bool_classifier
alias no_finite_history_classifier := SomControlV11.Derivation.no_finite_history_classifier

-- PSpace
alias generic_aspect_audit    := SomControlV11.PSpace.generic_aspect_audit
alias auditEq_implies_quot_eq := SomControlV11.PSpace.auditEq_implies_quot_eq

end SomControlV11.Release
