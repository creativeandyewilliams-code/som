import Mathlib
import SomControlV11.Temporal.RichWitness

/-!
# SomControlV11.Derivation.NoveltySeparation
NoveltySeparation: the V11 witness pair demonstrates that the orbit-target
predicate cannot be recovered from the observation history alone.

This is the core impossibility result from which audit-equivalent necessity
follows as a corollary.
-/

namespace SomControlV11.Derivation

open SomControlV11.Temporal

/-- Novelty separation: states xA and xB share their full observation history
    yet differ in their Below status. No observation-based rule can separate them. -/
theorem novelty_separation :
    ∃ x y : X, qInf x = qInf y ∧ (Below x ↔ ¬ Below y) :=
  ⟨xA, xB, hist_agree,
   ⟨fun _ => xB_not_Below, fun _ => xA_Below⟩⟩

/-- No Bool-valued function of the observation sequence can correctly classify
    the Below predicate: any such function either misclassifies xA or xB. -/
theorem no_obs_separator :
    ¬ ∃ d : (ℕ → Bool) → Bool,
      (d (qInf xA) = true ↔ Below xA) ∧
      (d (qInf xB) = true ↔ Below xB) := by
  intro ⟨d, ha, hb⟩
  have heq : qInf xA = qInf xB := hist_agree
  rw [heq] at ha
  have hBxA : Below xA := xA_Below
  have hnBxB : ¬ Below xB := xB_not_Below
  exact hnBxB (hb.mp (ha.mpr hBxA))

end SomControlV11.Derivation
