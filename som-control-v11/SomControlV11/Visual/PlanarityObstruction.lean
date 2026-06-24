import Mathlib
import SomControlV11.Visual.IncidenceGraph

/-!
# SomControlV11.Visual.PlanarityObstruction
K₅ planarity obstruction (excluded from release graph).

The complete graph K₅ is not planar (Kuratowski/Wagner). This is used
in V11 to show that the 5-node diagnostic topology cannot be realized
as a planar graph, motivating the R³ embedding.

**Status: PENDING** — K₅ non-planarity is not yet in Lean 4 Mathlib;
excluded from release graph.
-/

namespace SomControlV11.Visual

/-- K₅: the complete graph on 5 vertices. -/
def K5 : FinGraph := completeGraph 5

/-- K₅ is not planar.
    **Open obligation**: planarity theory (Kuratowski's theorem) is not yet
    available in Lean 4 Mathlib as of this writing. -/
theorem K5_not_planar :
    ¬ ∃ φ : K5.V → (Fin 2 → ℝ), Function.Injective φ ∧
      ∀ e₁ e₂ : K5.E, ¬ (∃ t s : Set.Icc (0:ℝ) 1,
        (1 - (t:ℝ)) • φ (K5.incidence e₁ 0) + (t:ℝ) • φ (K5.incidence e₁ 1) =
        (1 - (s:ℝ)) • φ (K5.incidence e₂ 0) + (s:ℝ) • φ (K5.incidence e₂ 1)) := by
  sorry

end SomControlV11.Visual
