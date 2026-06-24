import Mathlib

/-!
# SomControlV11.Visual.IncidenceGraph
Finite incidence graph structure for V11 visual geometry.

Defines a simple finite undirected graph structure used to represent
the diagnostic-output topology in the V11 visual companion.
-/

namespace SomControlV11.Visual

/-- A finite undirected graph: vertex type V, edge type E, incidence map. -/
structure FinGraph where
  V : Type*
  E : Type*
  incidence : E → Fin 2 → V

/-- An edge e is a loop at v. -/
def isLoop (G : FinGraph) (e : G.E) : Prop :=
  G.incidence e 0 = G.incidence e 1

/-- Vertices u and v are adjacent if some edge connects them. -/
def adjacent (G : FinGraph) (u v : G.V) : Prop :=
  ∃ e : G.E, (G.incidence e 0 = u ∧ G.incidence e 1 = v) ∨
             (G.incidence e 0 = v ∧ G.incidence e 1 = u)

/-- A graph coloring with k colors. -/
def Coloring (G : FinGraph) (k : ℕ) := G.V → Fin k

/-- A coloring is proper if no two adjacent vertices share a color. -/
def properColoring (G : FinGraph) (k : ℕ) (c : Coloring G k) : Prop :=
  ∀ u v : G.V, adjacent G u v → c u ≠ c v

/-- A graph embedding into a type T is a map from vertices that is injective. -/
def GraphEmbedding (G : FinGraph) (T : Type*) :=
  { φ : G.V → T // Function.Injective φ }

/-- An edge-separated embedding: no two non-adjacent vertices share an edge-midpoint
    (encoded as: the image of the incidence map for each edge is distinct). -/
def edgeSeparated (G : FinGraph) (T : Type*) (φ : G.V → T) : Prop :=
  ∀ e₁ e₂ : G.E, ∀ i j : Fin 2,
    φ (G.incidence e₁ i) = φ (G.incidence e₂ j) →
    G.incidence e₁ i = G.incidence e₂ j

/-- A complete graph on n vertices. -/
def completeGraph (n : ℕ) : FinGraph where
  V := Fin n
  E := { p : Fin n × Fin n // p.1 ≠ p.2 }
  incidence := fun ⟨⟨u, v⟩, _⟩ i => if i = 0 then u else v

theorem completeGraph_adjacent (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    adjacent (completeGraph n) u v :=
  ⟨⟨⟨u, v⟩, huv⟩, Or.inl ⟨rfl, rfl⟩⟩

end SomControlV11.Visual
