import Mathlib
import SomControlV11.Core.Factorization

/-!
# SomControlV11.Core.TypedRecord
Typed diagnostic status: descent, nondescent, incomplete.
Only descent and nondescent are mathematically certified; incomplete is an evidence state.
-/

namespace SomControlV11.Core

/-- A decoder certifying that T factors through q. -/
structure Decoder {α β γ : Type*} (q : α → β) (T : α → γ) where
  map        : β → γ
  factorizes : ∀ x, T x = map (q x)

/-- Three-way diagnostic status for target T relative to representation q.
    Only the first two constructors carry mathematical certificates. -/
inductive DiagnosticStatus {α β γ : Type*} (q : α → β) (T : α → γ) where
  | descent    : Decoder q T → DiagnosticStatus q T
  | nondescent : PairedCertificate q T → DiagnosticStatus q T
  | incomplete : DiagnosticStatus q T

/-- Soundness of descent: certified descent implies factorization. -/
theorem descent_sound {α β γ : Type*} {q : α → β} {T : α → γ}
    (d : Decoder q T) : ∃ f : β → γ, ∀ x, T x = f (q x) :=
  ⟨d.map, d.factorizes⟩

/-- Soundness of nondescent: certified nondescent implies non-factorization. -/
theorem nondescent_sound {α β γ : Type*} {q : α → β} {T : α → γ}
    (cert : PairedCertificate q T) : ¬ ∃ f : β → γ, ∀ x, T x = f (q x) :=
  no_factor_of_paired cert

end SomControlV11.Core
