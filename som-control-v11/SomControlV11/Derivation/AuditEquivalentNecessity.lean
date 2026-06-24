import Mathlib
import SomControlV11.Temporal.RichWitness

/-!
# SomControlV11.Derivation.AuditEquivalentNecessity
Audit-equivalent necessity: the orbit-target predicate requires latent-state
access and cannot be computed from audit-equivalent (observation-equivalent)
state information.

This is the V11 necessity claim: any correct predictor of Below must break
audit equivalence and access information beyond the observation history.
-/

namespace SomControlV11.Derivation

open SomControlV11.Temporal

/-- Audit-equivalent necessity: Below does not factor through the observation history.
    Restates orbit_target_no_factor in the necessity framing. -/
theorem audit_equivalent_necessity :
    ¬ ∃ d : (ℕ → Bool) → Prop, ∀ x : X, Below x ↔ d (qInf x) :=
  orbit_target_no_factor

/-- Bool-valued corollary: no decidable observation-based classifier agrees with Below. -/
theorem no_bool_classifier :
    ¬ ∃ d : (ℕ → Bool) → Bool, ∀ x : X, Below x ↔ (d (qInf x) = true) :=
  fun ⟨d, hd⟩ => audit_equivalent_necessity ⟨fun h => d h = true, hd⟩

/-- Finite-history corollary: for every n, no function of the n-step observation
    history classifies Below correctly on the canonical witness pair. -/
theorem no_finite_history_classifier (n : ℕ) :
    ¬ ∃ d : List Bool → Bool,
      (d (qFin n xA) = true ↔ Below xA) ∧
      (d (qFin n xB) = true ↔ Below xB) := by
  intro ⟨d, ha, hb⟩
  have heq : qFin n xA = qFin n xB := finHist_agree n
  rw [heq] at ha
  exact xB_not_Below (hb.mp (ha.mpr xA_Below))

end SomControlV11.Derivation
