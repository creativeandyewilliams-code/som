import Mathlib

/-!
# SomControlV11.Core.Factorization
Fiber criterion and paired non-descent certificate.
Provides reusable machinery for temporal, diagnostic, and derivational modules.
-/

namespace SomControlV11.Core

/-- T factors through q iff q-fibers are T-constant (fiber criterion). -/
theorem fiber_criterion {α β γ : Type*} (q : α → β) (T : α → γ) :
    (∃ d : β → γ, ∀ x, T x = d (q x)) ↔
    (∀ x y : α, q x = q y → T x = T y) := by
  constructor
  · rintro ⟨d, hd⟩ x y hxy
    rw [hd, hxy]
  · intro h
    refine ⟨fun b => if hb : ∃ x, q x = b then T hb.choose else Classical.arbitrary _, ?_⟩
    intro x
    simp only [dif_pos ⟨x, rfl⟩]
    exact h _ _ (Classical.choose_spec ⟨x, rfl⟩).symm

/-- A paired certificate: same q-image but different T-output witnesses non-factorization. -/
structure PairedCertificate {α β γ : Type*} (q : α → β) (T : α → γ) where
  witA     : α
  witB     : α
  histEq   : q witA = q witB
  targetNe : T witA ≠ T witB

theorem no_factor_of_paired {α β γ : Type*} {q : α → β} {T : α → γ}
    (cert : PairedCertificate q T) :
    ¬ ∃ d : β → γ, ∀ x, T x = d (q x) := by
  rintro ⟨d, hd⟩
  exact cert.targetNe (by rw [hd, cert.histEq, ← hd])

end SomControlV11.Core
