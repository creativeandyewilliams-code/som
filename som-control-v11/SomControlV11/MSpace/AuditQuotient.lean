import Mathlib
import SomControlV11.MSpace.AuditFamily

/-!
# SomControlV11.MSpace.AuditQuotient
Coarseness order: every audit-faithful representation retains
at least the distinctions made by the audit quotient.
-/

namespace SomControlV11.MSpace

/-- Every audit-faithful r is coarser than or equal to auditQuot in the factorization order:
    auditQuot factors through r (r makes at least the distinctions of auditQuot). -/
theorem auditQuot_is_coarsest {P R : Type*} (A : AuditFamily P) (r : P → R)
    (hr : AuditFaithful A r) :
    ∀ p q : P, auditQuot A p = auditQuot A q → r p = r q :=
  fun p q h => hr p q (auditEq_of_auditQuot_eq A h)

/-- Finite-population information bound: the quotient partitions a finite population. -/
theorem auditQuot_finite_partition {P : Type*} [Fintype P] (A : AuditFamily P) :
    Fintype.card (Quotient (auditEqSetoid A)) ≤ Fintype.card P :=
  Fintype.card_quotient_le _

end SomControlV11.MSpace
