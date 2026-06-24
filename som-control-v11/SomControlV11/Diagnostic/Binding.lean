import Mathlib
import SomControlV11.Core.Factorization

/-!
# SomControlV11.Diagnostic.Binding
Binding-sensitive diagnostic non-factorization.
Shows that a record-level diagnostic output does not factor through
the component-forgetting projection.
-/

namespace SomControlV11.Diagnostic

open SomControlV11.Core

/-- A channel record: observable components. -/
structure ChannelRecord where
  ch1 : Bool
  ch2 : Bool
  deriving DecidableEq

/-- A binding record: channel components plus a binding label. -/
structure BindingRecord where
  channels : ChannelRecord
  binding  : Bool

/-- Component-forgetting projection: drops the binding label. -/
def componentProj (r : BindingRecord) : ChannelRecord := r.channels

/-- Diagnostic output: depends on both channels and binding. -/
def diagnostic (r : BindingRecord) : Bool := r.binding && r.channels.ch1

/-- Two records with equal component projection but unequal diagnostic output. -/
def recA : BindingRecord := ⟨⟨true, false⟩, true⟩
def recB : BindingRecord := ⟨⟨true, false⟩, false⟩

lemma recAB_sameProj : componentProj recA = componentProj recB := rfl
lemma recA_diag : diagnostic recA = true := rfl
lemma recB_diag : diagnostic recB = false := rfl
lemma recAB_diffDiag : diagnostic recA ≠ diagnostic recB := by decide

/-- Binding-sensitive non-factorization:
    diagnostic does not factor through componentProj. -/
theorem binding_nonfactorization :
    ¬ ∃ d : ChannelRecord → Bool,
        ∀ r : BindingRecord, diagnostic r = d (componentProj r) :=
  no_factor_of_paired {
    witA     := recA
    witB     := recB
    histEq   := recAB_sameProj
    targetNe := recAB_diffDiag
  }

end SomControlV11.Diagnostic
