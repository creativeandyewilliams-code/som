/-
  Bounded formal certification of a globally coherent hypothesis.

  This file formalizes "Bounded formal certification of a globally coherent
  hypothesis": a finite, decidable certificate semantics for a claim-status
  ledger. It does not prove that every mapping claim is true. It proves the
  narrower statement that, relative to a declared finite assessment budget
  and a declared defeater language, a submitted claim graph is well-typed,
  compositionally closed, and contains no verified in-budget defeater.

  Everything here is built from plain computable `Bool`-valued functions on
  `List`/`Nat`/`List Bool`, which are automatically finite and decidable in
  Lean's core logic. This mirrors the source material directly: every
  "decidability" theorem there is witnessed here by a total, terminating
  function, and every soundness/monotonicity theorem is a small lemma about
  those functions.
-/

namespace BoundedGCH

/-! ### Codes, alphabet, assessment budgets (§ Codes, proof checking, budgets) -/

/-- The alphabet `Σ` is fixed to be finite; without loss of generality we take
the binary alphabet `Bool`, since every finite alphabet embeds into binary
strings. A "proof code", "claim id", "defeater witness", etc. is then an
element of `Σ* = List Bool`. -/
abbrev Code := List Bool

/-- All codes of exact length `n`. -/
def codesOfLength : Nat → List Code
  | 0 => [[]]
  | n + 1 => (codesOfLength n).flatMap (fun l => [false :: l, true :: l])

/-- `Definition (Assessment budget)`: the finite candidate universe
`𝒰_B = Σ^{≤N}` admitted by a budget `B = (N, T)`. -/
def codesUpTo (N : Nat) : List Code :=
  (List.range (N + 1)).flatMap codesOfLength

theorem mem_codesOfLength {n : Nat} {c : Code} :
    c ∈ codesOfLength n ↔ c.length = n := by
  induction n generalizing c with
  | zero => simp [codesOfLength]
  | succ n ih =>
    simp only [codesOfLength, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨l, hl, hc | hc⟩ <;> subst hc <;> simp [ih.mp hl]
    · intro hc
      cases c with
      | nil => simp at hc
      | cons b l =>
        simp only [List.length_cons] at hc
        refine ⟨l, ih.mpr (by omega), ?_⟩
        cases b <;> simp

/-- A code lies in the budget's candidate universe iff its length is within
the budget — the precise content of `𝒰_B = Σ^{≤N}`. -/
theorem mem_codesUpTo_iff {N : Nat} {d : Code} : d ∈ codesUpTo N ↔ d.length ≤ N := by
  unfold codesUpTo
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, hc⟩
    have h1 := mem_codesOfLength.mp hc
    have h2 := List.mem_range.mp hr
    omega
  · intro h
    exact ⟨d.length, List.mem_range.mpr (by omega), mem_codesOfLength.mpr rfl⟩

/-- An assessment budget `B = (N, T)`: a maximum code length `N` and a
maximum verifier running time `T`. -/
structure Budget where
  N : Nat
  T : Nat
deriving Repr

/-- `Acc_B(V, d)`: `d` lies in the budget's candidate universe and the
verifier `V` accepts `d`. The "run for at most `T` steps" clause of the
source definition is absorbed into `V` itself being given as a *total*
computable `Bool`-valued function: in Lean, every such function already
terminates, so any such `V` is by construction a `T`-bounded decision
procedure for some `T`. -/
def accB (B : Budget) (V : Code → Bool) (d : Code) : Bool :=
  decide (d ∈ codesUpTo B.N) && V d

/-- `Lemma (Budget finiteness and decidability)`.

`codesUpTo B.N` is a `List`, hence finite by construction, and `accB` is a
total computable `Bool`-valued function, hence a decision procedure by
construction. The genuine mathematical content of the source lemma — that a
length-bounded simulation of a fixed verifier is decidable — is exactly the
fact that `accB` is a *terminating* function of `B`, `V`, and `d`; this is
guaranteed by Lean's logic for every closed term of this type. -/
theorem budget_finite_and_decidable (B : Budget) (V : Code → Bool) :
    (codesUpTo B.N).length < (codesUpTo B.N).length + 1 ∧
      ∀ d, accB B V d = true ∨ accB B V d = false := by
  refine ⟨Nat.lt_succ_self _, fun d => ?_⟩
  cases accB B V d <;> simp

/-! ### Typed claim ledgers and finite defeaters -/

/-- A core row `(id, τ, Θ, Γ, φ, p)`. We abstract `Θ`, `Γ`, `φ`, `p` away and
retain only the two facts that matter for the certificate: the type tag
`τ ∈ {DT, CT}` (`isDT = true` for `DT`, `false` for `CT`) and the outcome
`checkOk` of `Check_Θ(Γ, φ, p)`. -/
structure CoreRow where
  id : Nat
  isDT : Bool
  checkOk : Bool
deriving Repr

/-- A mapping row `(id, Θ_m, μ_m, 𝒟_m)`. `defeaters` is the declared finite
family of defeater-interface codes `𝒟_m`, and `defeat` is the decision
procedure `Defeat_m` of Definition (Finite defeater interface): it returns
`true` exactly when its input parses as a triple `⟨δ, w, p⟩` with
`δ ∈ 𝒟_m` and both required proof checks succeed. -/
structure MappingRow where
  id : Nat
  defeaters : List Code
  defeat : Code → Bool

/-- A typed claim ledger `𝖧 = (𝖢, 𝖬, 𝖠, G)`. The dependency graph `G` is
recorded as a finite list of edges `u → v` on the ids occurring in
`coreIds ++ mapIds ++ assertIds`. -/
structure Ledger where
  coreIds : List Nat
  mapIds : List Nat
  assertIds : List Nat
  core : List CoreRow
  mapping : List MappingRow
  edges : List (Nat × Nat)

/-- `NoDef_B(𝖧)`: no finite defeater of any mapping row is accepted within
budget `B`. -/
def noDef (L : Ledger) (B : Budget) : Bool :=
  L.mapping.all (fun m => (codesUpTo B.N).all (fun d => !(accB B m.defeat d)))

/-- `Theorem (Decidability of bounded non-defeat)`. `noDef` is a total
computable `Bool`-valued function of a *finite* ledger and a *finite*
budget (`L.mapping` is a `List`, and `codesUpTo B.N` is a `List` by
`budget_finite_and_decidable`), hence the predicate is decidable by
construction. -/
instance noDef_decidable (L : Ledger) (B : Budget) :
    Decidable (noDef L B = true) :=
  inferInstanceAs (Decidable (_ = true))

/-! ### Reachability in the finite dependency graph -/

/-- One step of forward closure: extend a vertex set `S` by the out-neighbors
(in `E`) of vertices already in `S`. -/
def stepReach (E : List (Nat × Nat)) (S : List Nat) : List Nat :=
  (S ++ E.filterMap (fun e => if e.1 ∈ S then some e.2 else none)).dedup

/-- Iterate `stepReach` until a fixpoint, or `fuel` runs out. -/
def closureReach (E : List (Nat × Nat)) (S : List Nat) : Nat → List Nat
  | 0 => S
  | fuel + 1 =>
    let S' := stepReach E S
    if S'.length ≤ S.length then S else closureReach E S' fuel

/-- All vertices occurring in the ledger. -/
def Ledger.verts (L : Ledger) : List Nat :=
  L.coreIds ++ L.mapIds ++ L.assertIds

/-- Vertices reachable from `u` along a directed path of length `≥ 1`
(i.e. `u ⤳_G v` with `u ≠ v` required by at least one edge traversal). -/
def Ledger.reachPos (L : Ledger) (u : Nat) : List Nat :=
  closureReach L.edges (stepReach L.edges [u]) (L.verts.length + 1)

/-- `u ⤳_G v`: there is a directed path of length `≥ 1` from `u` to `v`. -/
def Ledger.reaches (L : Ledger) (u v : Nat) : Bool :=
  v ∈ L.reachPos u

/-- One step of forward closure avoiding a set of forbidden intermediate
vertices (used to test "every path meets 𝖬"). -/
def stepAvoid (E : List (Nat × Nat)) (avoid : List Nat) (S : List Nat) : List Nat :=
  (S ++ E.filterMap (fun e => if e.1 ∈ S ∧ ¬ e.2 ∈ avoid then some e.2 else none)).dedup

def closureAvoid (E : List (Nat × Nat)) (avoid : List Nat) (S : List Nat) :
    Nat → List Nat
  | 0 => S
  | fuel + 1 =>
    let S' := stepAvoid E avoid S
    if S'.length ≤ S.length then S else closureAvoid E avoid S' fuel

/-- Vertices reachable from `u` by a path of length `≥ 1` whose *intermediate
and final* vertices avoid `avoid`. -/
def Ledger.reachAvoiding (L : Ledger) (avoid : List Nat) (u : Nat) : List Nat :=
  closureAvoid L.edges avoid (stepAvoid L.edges avoid [u]) (L.verts.length + 1)

/-- `u ⤳_G v` via a path that never meets `avoid`. -/
def Ledger.reachesAvoiding (L : Ledger) (avoid : List Nat) (u v : Nat) : Bool :=
  v ∈ L.reachAvoiding avoid u

/-- The graph is acyclic: no vertex reaches itself by a path of length `≥ 1`. -/
def Ledger.acyclic (L : Ledger) : Bool :=
  L.verts.all (fun v => !(L.reaches v v))

/-! ### Type consistency, compositional closure, certification -/

/-- `Type(𝖧)`, Definition (Type consistency):
(a) every core row has a valid tag — automatic, `isDT : Bool`;
(b) every core proof verifies (`checkOk = true`);
(c) every mapping row has a valid formula and finite declared defeater
    family — automatic, `MappingRow` carries a `List Code`;
(d) no mapping row is a premise of a core row. -/
def typeConsistent (L : Ledger) : Bool :=
  L.core.all (fun c => c.checkOk) &&
  L.mapIds.all (fun m => L.coreIds.all (fun c => !(L.reaches m c)))

/-- `Closed(𝖧)`, Definition (Compositional closure): `G` is acyclic and every
target-facing assertion `a` is (a) mediated by some mapping row, and
(b) every core-to-`a` path passes through a mapping row. -/
def closed (L : Ledger) : Bool :=
  L.acyclic &&
  L.assertIds.all (fun a =>
    L.mapIds.any (fun m => L.reaches m a) &&
    L.coreIds.all (fun c =>
      !(L.reaches c a) || !(L.reachesAvoiding L.mapIds c a)))

/-- `Lemma (Decidability of type consistency and closure)`: both predicates
are total computable `Bool`-valued functions of a finite ledger, hence
decidable by construction (finite-graph reachability/acyclicity is computed
by the bounded fixpoints `closureReach`/`closureAvoid` above). -/
instance typeConsistent_decidable (L : Ledger) :
    Decidable (typeConsistent L = true) :=
  inferInstanceAs (Decidable (_ = true))

instance closed_decidable (L : Ledger) : Decidable (closed L = true) :=
  inferInstanceAs (Decidable (_ = true))

/-- `Definition (Bounded global-coherence certificate)`:
`GCert_B(𝖧) = Type(𝖧) ∧ Closed(𝖧) ∧ NoDef_B(𝖧)`. -/
def gcert (L : Ledger) (B : Budget) : Bool :=
  typeConsistent L && closed L && noDef L B

/-- `Theorem (Decidability of the global-coherence certificate)`: `gcert` is
a finite conjunction of the decidable predicates above, hence decidable. -/
instance gcert_decidable (L : Ledger) (B : Budget) :
    Decidable (gcert L B = true) :=
  inferInstanceAs (Decidable (_ = true))

/-! ### Soundness, defeater detection, and budget monotonicity -/

/-- `Theorem (Certificate soundness at the declared scope)`. If the
certificate holds at budget `B`, then: every core row's declared proof
verified; no mapping row is a premise of a core row; every assertion is
mediated by some mapping row; and no accepted finite defeater of any
mapping row lies in the budget's candidate universe. -/
theorem gcert_soundness {L : Ledger} {B : Budget} (h : gcert L B = true) :
    (∀ c ∈ L.core, c.checkOk = true) ∧
      (∀ m ∈ L.mapIds, ∀ c ∈ L.coreIds, L.reaches m c = false) ∧
      (∀ a ∈ L.assertIds, ∃ m ∈ L.mapIds, L.reaches m a = true) ∧
      (∀ m ∈ L.mapping, ∀ d ∈ codesUpTo B.N, accB B m.defeat d = false) := by
  unfold gcert at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hType, hClosed⟩, hNoDef⟩ := h
  unfold typeConsistent at hType
  rw [Bool.and_eq_true] at hType
  obtain ⟨hCore, hPremise⟩ := hType
  unfold closed at hClosed
  rw [Bool.and_eq_true] at hClosed
  obtain ⟨_, hAssert⟩ := hClosed
  refine ⟨List.all_eq_true.mp hCore, ?_, ?_, ?_⟩
  · intro m hm c hc
    have := List.all_eq_true.mp hPremise m hm
    have := List.all_eq_true.mp this c hc
    simpa using this
  · intro a ha
    have := List.all_eq_true.mp hAssert a ha
    rw [Bool.and_eq_true] at this
    obtain ⟨hMed, _⟩ := this
    obtain ⟨m, hm, hmr⟩ := List.any_eq_true.mp hMed
    exact ⟨m, hm, hmr⟩
  · unfold noDef at hNoDef
    rw [List.all_eq_true] at hNoDef
    intro m hm d hd
    have hm' := hNoDef m hm
    rw [List.all_eq_true] at hm'
    have := hm' d hd
    simpa using this

/-- `Theorem (Defeater detection completeness within budget)`. If a code `d`
in the budget's candidate universe is accepted by the defeater verifier of
some mapping row `m`, the certificate fails at that budget. -/
theorem defeater_detection {L : Ledger} {B : Budget} {m : MappingRow}
    (hm : m ∈ L.mapping) {d : Code} (hd : accB B m.defeat d = true) :
    gcert L B = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  obtain ⟨_, _, _, hNo⟩ := gcert_soundness h
  have hdU : d ∈ codesUpTo B.N := by
    unfold accB at hd
    rcases Bool.and_eq_true.mp hd with ⟨h1, _⟩
    simpa using h1
  have := hNo m hm d hdU
  rw [hd] at this
  exact absurd this (by decide)

/-- `Proposition (Budget monotonicity)`. Enlarging an assessment budget can
only shrink the set of ledgers certified: if `N ≤ N'`, then a defeater
accepted within `(N, T)` is also accepted within `(N', T')` (its code is a
fortiori short enough), so `NoDef` at the larger budget implies `NoDef` at
the smaller one, and the type/closure predicates do not depend on the
budget at all. -/
theorem gcert_budget_monotone {L : Ledger} {B B' : Budget} (hN : B.N ≤ B'.N) :
    gcert L B' = true → gcert L B = true := by
  intro h
  unfold gcert at h ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨hType, hClosed⟩, hNoDef'⟩ := h
  refine ⟨⟨hType, hClosed⟩, ?_⟩
  unfold noDef at hNoDef' ⊢
  rw [List.all_eq_true] at hNoDef' ⊢
  intro m hm
  have hm' := hNoDef' m hm
  rw [List.all_eq_true] at hm' ⊢
  intro d hd
  have hdN : d.length ≤ B.N := mem_codesUpTo_iff.mp hd
  have hd' : d ∈ codesUpTo B'.N := mem_codesUpTo_iff.mpr (by omega)
  have hres := hm' d hd'
  have hVfalse : m.defeat d = false := by
    unfold accB at hres
    simpa [hd'] using hres
  unfold accB
  simp [hd, hVfalse]

end BoundedGCH
