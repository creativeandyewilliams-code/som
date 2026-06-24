import Mathlib
import SomControlV11.Core.Factorization

/-!
# SomControlV11.Core.DecisionPartitions
Kernel equivalence and coarsest decision partition.
-/

namespace SomControlV11.Core

/-- The kernel relation of T: x ~ y iff T x = T y. -/
def kernelRel {α γ : Type*} (T : α → γ) : α → α → Prop := fun x y => T x = T y

theorem kernelRel_equivalence {α γ : Type*} (T : α → γ) :
    Equivalence (kernelRel T) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- q refines the T-kernel iff T factors through q. -/
theorem refines_iff_factors {α β γ : Type*} (q : α → β) (T : α → γ) :
    (∀ x y, q x = q y → kernelRel T x y) ↔
    ∃ d : β → γ, ∀ x, T x = d (q x) :=
  (fiber_criterion q T).symm

/-- T itself is the coarsest representation through which T factors. -/
theorem T_factors_through_self {α γ : Type*} (T : α → γ) :
    ∃ d : γ → γ, ∀ x, T x = d (T x) :=
  ⟨id, fun _ => rfl⟩

/-- Every factorization through q refines the kernel of T. -/
theorem factorization_refines_kernel {α β γ : Type*} (q : α → β) (T : α → γ)
    (hq : ∃ d : β → γ, ∀ x, T x = d (q x)) :
    ∀ x y, q x = q y → kernelRel T x y := by
  obtain ⟨d, hd⟩ := hq
  intro x y hxy
  simp only [kernelRel, hd, hxy]

end SomControlV11.Core
