import Mathlib
import SomControlV11.MSpace.AuditFamily

/-!
# SomControlV11.PSpace.GenericAspectAudit
Generic aspect-audit separation theorem.

If two states p, q in a topological space P are separated by some auditor
in the audit family A (i.e., some f ∈ A satisfies f p ≠ f q), then their
audit quotient images are distinct. This is the separation direction of
audit-equivalence: the audit quotient does not collapse auditor-distinct states.

Note: The converse (if audit-equivalent then quotient-identified) is definitional.
The full continuity/compactness theory for the quotient topology is a separate
pending project (Level B).
-/

namespace SomControlV11.PSpace

open SomControlV11.MSpace

/-- A continuous audit family: all auditors are continuous. -/
def ContinuousAuditFamily {P : Type*} [TopologicalSpace P]
    (A : AuditFamily P) : Prop :=
  ∀ f ∈ A, Continuous f

/-- Generic aspect-audit separation: if p and q are separated by some auditor,
    their audit quotient images are distinct.

    This is the point-separation direction of the audit quotient construction:
    the quotient faithfully remembers all auditor distinctions. -/
theorem generic_aspect_audit {P : Type*}
    (A : AuditFamily P)
    (p q : P) (h : ∃ f ∈ A, f p ≠ f q) :
    auditQuot A p ≠ auditQuot A q := by
  intro heq
  obtain ⟨f, hf, hfpq⟩ := h
  exact hfpq (Quotient.exact heq f hf)

/-- Converse direction (definitional): audit-equivalent states map to the same quotient point. -/
theorem auditEq_implies_quot_eq {P : Type*} (A : AuditFamily P) {p q : P}
    (h : AuditEq A p q) : auditQuot A p = auditQuot A q :=
  Quotient.sound h

end SomControlV11.PSpace
