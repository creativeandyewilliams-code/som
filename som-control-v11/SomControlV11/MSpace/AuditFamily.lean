import Mathlib

/-!
# SomControlV11.MSpace.AuditFamily
Audit family, audit equivalence, and coarsest audit-faithful quotient.
-/

namespace SomControlV11.MSpace

/-- An audit family on P: a set of Bool-valued audit functions. -/
def AuditFamily (P : Type*) := Set (P → Bool)

/-- Audit equivalence: p ~ q iff every auditor returns the same output. -/
def AuditEq {P : Type*} (A : AuditFamily P) (p q : P) : Prop :=
  ∀ auditor ∈ A, auditor p = auditor q

theorem auditEq_refl {P : Type*} (A : AuditFamily P) (p : P) :
    AuditEq A p p := fun _ _ => rfl

theorem auditEq_symm {P : Type*} (A : AuditFamily P) {p q : P}
    (h : AuditEq A p q) : AuditEq A q p :=
  fun a ha => (h a ha).symm

theorem auditEq_trans {P : Type*} (A : AuditFamily P) {p q r : P}
    (h1 : AuditEq A p q) (h2 : AuditEq A q r) : AuditEq A p r :=
  fun a ha => (h1 a ha).trans (h2 a ha)

/-- Audit equivalence setoid. -/
def auditEqSetoid {P : Type*} (A : AuditFamily P) : Setoid P where
  r     := AuditEq A
  iseqv := ⟨auditEq_refl A, fun h => auditEq_symm A h,
            fun h1 h2 => auditEq_trans A h1 h2⟩

/-- Audit-faithful representation: audit-equivalent points map to equal outputs. -/
def AuditFaithful {P R : Type*} (A : AuditFamily P) (r : P → R) : Prop :=
  ∀ p q : P, AuditEq A p q → r p = r q

/-- The audit quotient: canonical audit-faithful representation. -/
def auditQuot {P : Type*} (A : AuditFamily P) : P → Quotient (auditEqSetoid A) :=
  Quotient.mk (auditEqSetoid A)

theorem auditQuot_faithful {P : Type*} (A : AuditFamily P) :
    AuditFaithful A (auditQuot A) :=
  fun p q h => Quotient.sound h

/-- The audit quotient is coarsest: every audit-faithful r factors through auditQuot. -/
theorem coarsest_audit_faithful {P R : Type*} (A : AuditFamily P) (r : P → R)
    (hr : AuditFaithful A r) :
    ∃ d : Quotient (auditEqSetoid A) → R, ∀ p, r p = d (auditQuot A p) :=
  ⟨Quotient.lift r (fun p q h => hr p q h), fun _ => rfl⟩

/-- Audit-equivalent points have equal auditQuot image. -/
theorem auditQuot_eq_of_auditEq {P : Type*} (A : AuditFamily P) {p q : P}
    (h : AuditEq A p q) : auditQuot A p = auditQuot A q :=
  Quotient.sound h

/-- Equal auditQuot images imply audit equivalence. -/
theorem auditEq_of_auditQuot_eq {P : Type*} (A : AuditFamily P) {p q : P}
    (h : auditQuot A p = auditQuot A q) : AuditEq A p q :=
  Quotient.exact h

end SomControlV11.MSpace
