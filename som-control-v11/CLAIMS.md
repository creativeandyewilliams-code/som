# SomControlV11 Formal Companion — V11 Claims Manifest

Build target: `lake build SomControlV11.Release.V11Claims`

## Verified declarations (no sorry, no admit)

| V11 source | Lean declaration | File | Status |
|---|---|---|---|
| thm:fiber (fiber criterion) | `SomControlV11.Core.fiber_criterion` | `Core/Factorization.lean` | Checked |
| Paired certificate soundness | `SomControlV11.Core.no_factor_of_paired` | `Core/Factorization.lean` | Checked |
| Descent soundness | `SomControlV11.Core.descent_sound` | `Core/TypedRecord.lean` | Checked |
| Nondescent soundness | `SomControlV11.Core.nondescent_sound` | `Core/TypedRecord.lean` | Checked |
| Coarsest decision partition | `SomControlV11.Core.factorization_refines_kernel` | `Core/DecisionPartitions.lean` | Checked |
| thm:rich (rich temporal non-descent) | `SomControlV11.Temporal.rich_nondescent` | `Temporal/RichWitness.lean` | Checked |
| Dyadic xA Below | `SomControlV11.Temporal.xA_Below` | `Temporal/RichWitness.lean` | Checked |
| Dyadic xB AtOne | `SomControlV11.Temporal.xB_AtOne` | `Temporal/RichWitness.lean` | Checked |
| Monitor decoder | `SomControlV11.Temporal.monitor_decoder` | `Temporal/RichWitness.lean` | Checked |
| Strict history refinement | `SomControlV11.Temporal.history_strictly_refines` | `Temporal/RichWitness.lean` | Checked |
| Orbit target non-factorization | `SomControlV11.Temporal.orbit_target_no_factor` | `Temporal/RichWitness.lean` | Checked |
| thm:binding (binding non-factorization) | `SomControlV11.Diagnostic.binding_nonfactorization` | `Diagnostic/Binding.lean` | Checked |
| V11 coding reduction (Level A) | `SomControlV11.ReverseMath.coding_correct` | `ReverseMath/CodingReduction.lean` | Checked |
| Audit quotient faithful | `SomControlV11.MSpace.auditQuot_faithful` | `MSpace/AuditFamily.lean` | Checked |
| Audit quotient coarsest | `SomControlV11.MSpace.coarsest_audit_faithful` | `MSpace/AuditFamily.lean` | Checked |
| Coarseness order | `SomControlV11.MSpace.auditQuot_is_coarsest` | `MSpace/AuditQuotient.lean` | Checked |
| Finite partition bound | `SomControlV11.MSpace.auditQuot_finite_partition` | `MSpace/AuditQuotient.lean` | Checked |
| thm:debt Debt recurrence | `SomControlV11.Ledger.debt_diverges` | `Ledger/DebtRecurrence.lean` | Checked |
| Debt stable repair | `SomControlV11.Ledger.debt_stable_when_within_capacity` | `Ledger/DebtRecurrence.lean` | Checked |
| thm:capacity Capacity dominance | `SomControlV11.Ledger.auditQuot_capacity_dominance` | `Ledger/CapacityDominance.lean` | Checked (conditional on cost monotonicity hypothesis) |

## Pending (sorry, excluded from release graph)

| V11 source | Pending declaration | Reason |
|---|---|---|
| lem:3d-v9, thm:3dmin-v9 | R³ edge-separated embedding | Requires Vandermonde determinant / moment curve argument |
| K₅ lower bound | Planarity obstruction | Requires formal planar graph theory |
| thm:ugap (UGapTail ↔ ACA₀) | ACA0Equivalence | Level B: requires formalized RCA₀ metatheory |
| thm:pspace | GenericAspectAudit | Pending parameterized instantiation |

## Explicitly excluded (empirical bridge)

Corpus forecasts, human performance claims, repository ledger measurements,
and 3D interface effects are preregistered empirical hypotheses. They are
not theorem certificates and are not included in this package.

## Axiom report

All public theorems in the release graph rely only on:
- `Classical.choice`
- `propext`
- `Quot.sound`
- `funext`

No additional trusted axioms. The presence of `Classical.choice` is expected
and reflects standard mathematical practice (coarsest-partition construction,
quotient lift). It is not a defect.

## Reverse mathematics boundary

`CodingReduction.lean` proves the V11 coding construction and gap lemmas in
Lean’s ambient metatheory. This is **not** a proof over RCA₀. The paper’s
claim `UGapTail ↔ ACA₀` remains an ordinary mathematical proof until Level B
(a formalized RCA₀ derivability result) is completed.
