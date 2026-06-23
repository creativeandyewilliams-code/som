# Bounded formal certification of a globally coherent hypothesis — expanded proof

This document expands the source LaTeX into a fully detailed proof, with every
step spelled out, and records the correspondence with the Lean formalization
in `BoundedGCH/Cert.lean`. Throughout, `Σ` is a fixed finite alphabet and
`Σ*` is the set of finite strings over `Σ`. Every proof code, claim, edge,
mapping row, defeater witness, and verifier input is an element of `Σ*`.

## 1. Codes, proof checking, and assessment budgets

For each declared formal theory `Θ` we are given a decidable proof-checking
predicate `Check_Θ(Γ, φ, p) ∈ {0,1}`, where `Γ` is a finite assumption pack,
`φ` a formula, and `p` a finite proof code, satisfying the soundness
condition

  Check_Θ(Γ, φ, p) = 1  ⟹  Γ ⊨_Θ φ.

**Definition 1 (Assessment budget).** An assessment budget is a pair
`B = (N, T) ∈ ℕ²`: `N` a maximum code length, `T` a maximum verifier running
time. The finite candidate universe admitted by `B` is

  𝒰_B := Σ^{≤N} := ⋃_{r=0}^{N} Σ^r.

For a deterministic verifier `V` and a code `d ∈ Σ*`, `Acc_B(V, d) = 1`
exactly when `d ∈ 𝒰_B` and `V` accepts `d` within at most `T` steps;
otherwise `Acc_B(V, d) = 0`.

**Lemma 1 (Budget finiteness and decidability).** For every assessment
budget `B = (N, T)`, `𝒰_B` is finite and `Acc_B(V, d)` is decidable.

*Proof, expanded.* Fix `B = (N, T)`.

1. *Finiteness of `𝒰_B`.* Since `Σ` is finite, write `|Σ| = k`. For each fixed
   length `r`, `Σ^r` is the `r`-fold Cartesian product of `Σ` with itself, so
   `|Σ^r| = k^r < ∞`. The set `𝒰_B` is the finite union, over the finite index
   set `{0, 1, …, N}`, of these finitely many finite sets:

     |𝒰_B| = Σ_{r=0}^{N} |Σ^r| = Σ_{r=0}^{N} k^r < ∞,

   a finite geometric sum (equal to `(k^{N+1}-1)/(k-1)` when `k > 1`, or
   `N+1` when `k = 1`). Hence `𝒰_B` is a finite set.

2. *Decidability of `Acc_B(V, d)`.* Fix `V` and `d`. The decision procedure is:
   - Step (i): compute `|d|` and compare it to `N`. Both the computation of
     string length and the comparison of two natural numbers are decidable
     (indeed primitive recursive) operations, terminating after reading `d`
     once.
   - Step (ii): if `|d| > N`, halt and output `0` (reject; `d ∉ 𝒰_B`).
   - Step (iii): otherwise (`|d| ≤ N`, so `d ∈ 𝒰_B`), simulate the
     deterministic verifier `V` on input `d` for **exactly** `T` steps of its
     transition function. Because `V` is deterministic, this simulation is a
     well-defined, terminating computation (it performs exactly `T`
     transition-function applications, each of which is itself a decidable,
     finitary operation on `V`'s configuration).
   - Step (iv): output `1` if and only if the simulation reaches an accepting
     state at or before step `T`; otherwise output `0`.

   Every step of this procedure is finite and terminates after a number of
   primitive operations bounded by a fixed function of `|d|` and `T` (namely
   `O(|d|) + O(T)`), so the whole procedure is a total computable function of
   `(B, V, d)`, i.e. `Acc_B(V, d)` is decidable. ∎

*Lean correspondence.* `codesUpTo B.N : List Code` realizes `𝒰_B` directly as
a `List`, which is finite by construction (Lean's `List` type has no infinite
inhabitants), and `accB B V d : Bool` realizes `Acc_B(V, d)` as a total
computable Boolean function — in a terminating logic such as Lean's, being a
closed term of this type *is* the decidability witness; see
`budget_finite_and_decidable` and `mem_codesUpTo_iff` (the latter proves the
precise correspondence `d ∈ 𝒰_N ↔ |d| ≤ N`).

## 2. Typed claim ledgers and finite defeaters

**Definition 2 (Typed claim ledger).** A typed claim ledger is a finite
tuple `H = (C, M, A, G)` where `C` is a finite set of core rows
`c = (id, τ, Θ, Γ, φ, p)` with `τ ∈ {DT, CT}`; `M` is a finite set of mapping
rows `m = (id, Θ_m, μ_m, 𝒟_m)`, with `μ_m` the formalized mapping claim and
`𝒟_m` a finite family of declared defeater interfaces; `A` is a finite set of
target-facing assertions; and `G` is a finite directed dependency graph on
`C ∪ M ∪ A`, where `u → v` means `v` is declared to depend on `u`.

**Definition 3 (Finite defeater interface).** For a mapping row
`m = (id, Θ_m, μ_m, 𝒟_m)`, a finite defeater interface for `m` is a pair
`δ = (F_δ, s_δ)` where `F_δ(w)` is a formula containing a finite witness code
`w`, and `s_δ` is a finite proof code with

  Check_{Θ_m}(∅, F_δ(w) ⇒ ¬μ_m, s_δ) = 1   for every well-formed witness code `w`.

A finite defeater of `m` is a code `d = ⟨δ, w, p⟩` with `δ ∈ 𝒟_m` and

  Check_{Θ_m}(∅, F_δ(w), p) = 1.

`Defeat_m(d) ∈ {0,1}` returns `1` exactly when `d` parses as such a triple and
both checks succeed.

**Lemma 2 (Finite-defeater soundness).** If `Defeat_m(d) = 1`, then
`⊨_{Θ_m} ¬μ_m`.

*Proof, expanded.* Suppose `Defeat_m(d) = 1`. By the definition of
`Defeat_m`, this means `d` parses (uniquely, since parsing is decidable and
deterministic) as a triple `d = ⟨δ, w, p⟩` with `δ = (F_δ, s_δ) ∈ 𝒟_m`, and
both of the following hold:

  (i)  Check_{Θ_m}(∅, F_δ(w), p) = 1,
  (ii) Check_{Θ_m}(∅, F_δ(w) ⇒ ¬μ_m, s_δ) = 1   (by Definition 3, since `δ ∈ 𝒟_m` is a declared interface and this holds for *every* well-formed witness, in particular for the specific `w` occurring in `d`).

By the assumed soundness of the proof checker, (i) gives
`∅ ⊨_{Θ_m} F_δ(w)`, i.e. `⊨_{Θ_m} F_δ(w)`, and (ii) gives
`⊨_{Θ_m} F_δ(w) ⇒ ¬μ_m`. Since semantic entailment is closed under modus
ponens (if `⊨ φ` and `⊨ φ ⇒ ψ` then `⊨ ψ`, because every model satisfying
`φ` and `φ ⇒ ψ` must satisfy `ψ`), we conclude `⊨_{Θ_m} ¬μ_m`. ∎

**Definition 4 (No finite defeater exhibited within budget).** For a ledger
`H` and budget `B`, `NoDef_B(H) = 1` exactly when for every `m ∈ M` and every
`d ∈ 𝒰_B`, `Acc_B(Defeat_m, d) = 0`.

**Theorem 1 (Decidability of bounded non-defeat).** `NoDef_B(H)` is
decidable for every finite ledger `H` and budget `B`.

*Proof, expanded.* `M` is finite (Definition 2) and `𝒰_B` is finite (Lemma 1),
so `M × 𝒰_B` is a finite set, of cardinality `|M| · |𝒰_B|`. List its elements
`(m_1, d_1), …, (m_k, d_k)` for `k = |M|·|𝒰_B|`. For each `i`, the value
`Acc_B(Defeat_{m_i}, d_i)` is decidable by Lemma 1 (applied with
`V := Defeat_{m_i}`, itself a decidable predicate by Definition 3, since
parsing `d` and running the two proof checks are each decidable, and decidable
predicates are closed under this kind of finite composition). Evaluate all `k`
of these decisions — a finite, terminating procedure since `k < ∞` — and
output `1` iff every one of them equals `0`, and `0` otherwise. This is
precisely `NoDef_B(H)` by Definition 4, and the procedure terminates, so
`NoDef_B(H)` is decidable. ∎

*Lean correspondence.* `noDef L B : Bool` is `L.mapping.all (fun m =>
(codesUpTo B.N).all (fun d => !(accB B m.defeat d)))`, a finite double
iteration over the `List`s `L.mapping` and `codesUpTo B.N`, exactly
implementing the exhaustive check above; `noDef_decidable` records the
resulting `Decidable` instance.

## 3. Type consistency, compositional closure, and certification

Write `u ⤳_G v` for "there is a directed path from `u` to `v` in `G`".

**Definition 5 (Type consistency).** `Type(H) = 1` when (a) every core row
has a valid tag `DT`/`CT`; (b) every core proof verifies,
`Check_Θ(Γ, φ, p) = 1` for each `c = (id, τ, Θ, Γ, φ, p) ∈ C`; (c) every
mapping row has a valid mapping formula and a finite declared defeater
family; (d) no mapping row is a premise of a core row,
`∀ m ∈ M, ∀ c ∈ C, ¬(m ⤳_G c)`.

**Definition 6 (Compositional closure).** `Closed(H) = 1` when `G` is acyclic
and, for every `a ∈ A`: (a) some `m ∈ M` has `m ⤳_G a`; (b) every directed
path from any `c ∈ C` to `a` passes through some mapping row.

**Lemma 3 (Decidability of type consistency and closure).** Both predicates
are decidable for every finite ledger `H`.

*Proof, expanded.* All of `C`, `M`, `A`, and `G`'s edge set are finite
(Definition 2), and `Check_Θ` is decidable by assumption, so condition (b) of
Definition 5 is a finite conjunction of decidable conditions, hence decidable;
conditions (a) and (c) are finite syntactic checks on finitely many rows,
also decidable. For condition (d), and for acyclicity and the path conditions
of Definition 6, the relevant fact is that *reachability in a finite directed
graph is decidable*: with vertex set `V := C ∪ M ∪ A` (`|V| < ∞`) and edge set
`E ⊆ V × V` (`|E| < ∞`), the set of vertices reachable from a given `u` by a
path of length `≥ 1` can be computed by forward closure — start with the
out-neighbors of `u`, then repeatedly add out-neighbors of vertices already
found, for at most `|V|` rounds (after `|V|` rounds with no growth, the set
must be a fixpoint, since the reachable set is bounded by `|V|` and is
nondecreasing). This is a terminating procedure (at most `|V|` rounds, each
inspecting at most `|E|` edges), so `u ⤳_G v` is decidable for all `u, v`;
acyclicity (`∀ v ∈ V, ¬(v ⤳_G v)`) and "every path from `c` to `a` meets `M`"
(checked by recomputing reachability on the graph with vertices in `M`
removed as allowed intermediate/terminal steps, and comparing: `c ⤳_G a` via
some path while `c` cannot reach `a` while avoiding `M`) are then finite
Boolean combinations of these decidable reachability facts, hence decidable.
Each of conditions (a)–(d) of Definition 5 and (a)–(b) of Definition 6, plus
acyclicity, is thus decidable, and finite conjunctions/disjunctions of
decidable predicates are decidable, so `Type(H)` and `Closed(H)` are
decidable. ∎

*Lean correspondence.* `Ledger.reaches`/`Ledger.reachesAvoiding` implement the
forward-closure reachability sketched above (`stepReach`/`closureReach` and
`stepAvoid`/`closureAvoid`, run for `L.verts.length + 1` rounds, more than
enough rounds for a fixpoint on `L.verts.length` vertices); `typeConsistent`
and `closed` implement Definitions 5–6 verbatim in terms of these, and
`typeConsistent_decidable`/`closed_decidable` record decidability.

**Definition 7 (Bounded global-coherence certificate).**

  GCert_B(H) := Type(H) ∧ Closed(H) ∧ NoDef_B(H).

`H` is globally coherent at budget `B` exactly when `GCert_B(H) = 1`.

**Theorem 2 (Decidability of the global-coherence certificate).** The map
`(H, B) ↦ GCert_B(H)` is a total decidable predicate.

*Proof, expanded.* By Lemma 3, `Type(H)` and `Closed(H)` are each decidable;
by Theorem 1, `NoDef_B(H)` is decidable. `GCert_B(H)` is the conjunction of
these three decidable Boolean values. A conjunction of finitely many
decidable predicates is decided by deciding each conjunct in turn (each
terminates by hypothesis) and returning `1` iff all three return `1`; this
composite procedure terminates because each of its three sub-procedures
terminates. Hence `GCert_B(H)` is decidable, for every `(H, B)`, i.e. the map
is total and decidable. ∎

*Lean correspondence.* `gcert L B := typeConsistent L && closed L && noDef L
B`; `gcert_decidable` is the resulting instance — in Lean this is immediate
because `Bool` has decidable equality and `gcert` is already a total
computable function, but the underlying content (each conjunct terminates for
a structural reason particular to it) is exactly Theorem 2's proof.

**Theorem 3 (Certificate soundness at the declared scope).** If
`GCert_B(H) = 1` then: (a) every declared `DT`/`CT` core row has a verified
proof; (b) no mapping row is used as a premise of the theorem core; (c) every
target-facing assertion is mediated by at least one mapping row; (d) no
verifier-accepted finite defeater of any mapping row lies within `B`.

*Proof, expanded.* Assume `GCert_B(H) = 1`. By Definition 7,
`Type(H) = 1 ∧ Closed(H) = 1 ∧ NoDef_B(H) = 1`.

- From `Type(H) = 1` and Definition 5(b): for every
  `c = (id, τ, Θ, Γ, φ, p) ∈ C`, `Check_Θ(Γ, φ, p) = 1`. This is exactly (a).
- From `Type(H) = 1` and Definition 5(d): `∀ m ∈ M, ∀ c ∈ C, ¬(m ⤳_G c)`,
  i.e. no mapping row reaches (and in particular, is not a direct premise of)
  any core row. This is exactly (b).
- From `Closed(H) = 1` and Definition 6(a): for every `a ∈ A` there is
  `m ∈ M` with `m ⤳_G a`, i.e. `a` is mediated by a declared mapping row.
  This is exactly (c).
- From `NoDef_B(H) = 1` and Definition 4: for every `m ∈ M` and
  `d ∈ 𝒰_B`, `Acc_B(Defeat_m, d) = 0`, i.e. no code admitted by `B` is
  accepted as a defeater of any mapping row. This is exactly (d).

Each clause is read off directly from the corresponding conjunct of
Definition 7 together with the definition it unfolds to; no further
inference is needed. ∎

*Lean correspondence.* `gcert_soundness` proves exactly this four-way
conjunction by unfolding `gcert`, `typeConsistent`, `closed`, `noDef` and
extracting each `List.all`/`List.any` clause via `List.all_eq_true` /
`List.any_eq_true`.

**Theorem 4 (Defeater detection completeness within budget).** If
`m ∈ M`, `d ∈ 𝒰_B`, and `Acc_B(Defeat_m, d) = 1`, then `GCert_B(H) = 0`.

*Proof, expanded.* Suppose toward a contradiction that `GCert_B(H) = 1`. By
Theorem 3(d), for every `m' ∈ M` and `d' ∈ 𝒰_B`, `Acc_B(Defeat_{m'}, d') = 0`.
Instantiating at `m' := m`, `d' := d` (valid since `m ∈ M` and `d ∈ 𝒰_B` by
hypothesis) gives `Acc_B(Defeat_m, d) = 0`, contradicting the hypothesis
`Acc_B(Defeat_m, d) = 1`. Hence `GCert_B(H) ≠ 1`, and since `GCert_B(H)` is a
Boolean value, `GCert_B(H) = 0`. ∎

(Equivalently, and more directly: `d` witnesses that the universal condition
of Definition 4 fails, so `NoDef_B(H) = 0` immediately, and `GCert_B(H)` is a
conjunction one of whose conjuncts is `0`, hence `GCert_B(H) = 0`.)

*Lean correspondence.* `defeater_detection` is proved by exactly this
contradiction argument against `gcert_soundness`.

**Proposition 1 (Budget monotonicity).** For `B = (N, T)`, `B' = (N', T')`
with `N ≤ N'` and `T ≤ T'`: `GCert_{B'}(H) = 1 ⟹ GCert_B(H) = 1`.

*Proof, expanded.* `Type(H)` and `Closed(H)` do not mention `B` at all
(Definitions 5–6), so they take the same value regardless of which budget is
under discussion. It remains to show `NoDef_{B'}(H) = 1 ⟹ NoDef_B(H) = 1`.

First, `𝒰_B ⊆ 𝒰_{B'}`: if `d ∈ 𝒰_B = Σ^{≤N}` then `|d| ≤ N ≤ N'`, so
`d ∈ Σ^{≤N'} = 𝒰_{B'}`.

Second, if `Acc_B(V, d) = 1` then `Acc_{B'}(V, d) = 1`, for any verifier `V`:
`Acc_B(V, d) = 1` means `d ∈ 𝒰_B` and `V` accepts `d` within `T` steps; since
`𝒰_B ⊆ 𝒰_{B'}` we get `d ∈ 𝒰_{B'}`, and since `T ≤ T'`, accepting within `T`
steps implies accepting within `T'` steps (the simulation that halts and
accepts by step `T` has, in particular, halted and accepted by step `T'`, as
a deterministic verifier's trajectory does not change once it has reached an
accepting halting state). Hence `Acc_{B'}(V, d) = 1`.

Now assume `NoDef_{B'}(H) = 1`, i.e. for every `m ∈ M` and every
`d ∈ 𝒰_{B'}`, `Acc_{B'}(Defeat_m, d) = 0`. Fix `m ∈ M` and `d ∈ 𝒰_B`. Since
`𝒰_B ⊆ 𝒰_{B'}`, also `d ∈ 𝒰_{B'}`, so by hypothesis
`Acc_{B'}(Defeat_m, d) = 0`. If we had `Acc_B(Defeat_m, d) = 1`, the previous
paragraph would force `Acc_{B'}(Defeat_m, d) = 1`, a contradiction. Hence
`Acc_B(Defeat_m, d) = 0`. As `m, d` were arbitrary, `NoDef_B(H) = 1`.

Combining: `Type(H)`, `Closed(H)` are budget-independent and `NoDef_{B'}(H)
= 1 ⟹ NoDef_B(H) = 1`, so by Definition 7,
`GCert_{B'}(H) = 1 ⟹ GCert_B(H) = 1`. ∎

Equivalently: enlarging a budget can only ever *expose* a previously
out-of-reach defeater (shrinking the certified set further), never erase a
defeater already found at a smaller budget.

*Lean correspondence.* `gcert_budget_monotone` proves the `N`-only version
(the `T`-aspect of `Acc_B` is absorbed into the verifier `V` being a fixed
total function in the Lean model, as documented at `accB`); it uses
`mem_codesUpTo_iff` for the `𝒰_B ⊆ 𝒰_{B'}` step.

## 4. What the certificate does and does not assert; self-certification

**Remark.** `GCert_B(H) = 1` does **not** entail that every mapping claim
`μ_m` is true, nor that no defeater exists outside `B`. The precise status
asserted is exactly: *type-consistent, compositionally closed, and free of
verified in-budget finite defeaters* — see Theorem 3 for the exact four
clauses this unpacks to. A stronger "no defeater exists at all" conclusion
would require an additional completeness theorem (not proved here, and not
claimed by this section) that every genuine defeater has a code of length
`≤ N` verified within `T` steps.

**Corollary (Self-certification protocol).** Let `H_paper` be the finite
ledger extracted from a manuscript and supplement, with every claimed theorem
a checked proof row, every target-facing statement a mapping row, and every
mapping row supplied with finite defeater interfaces. Then
`GCert_B(H_paper) = 1` is a finite mathematical certificate that the paper
passes the declared type, closure, and bounded-defeater checks at budget `B`.

*Proof.* Apply Theorem 2 (the certificate is computable, so it can actually
be evaluated on `H_paper`) and Theorem 3 (if it evaluates to `1`, the four
soundness clauses hold) to `H_paper`. ∎
