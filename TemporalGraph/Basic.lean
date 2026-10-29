/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Init
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card

/-!
# Temporal graphs

This module defines temporal graphs on a vertex type `V`: a relation `Adj : V → V → ℕ → Prop`
recording, for each pair of vertices, the times at which an edge between them exists. Unlike
Mathlib's `SimpleGraph`, no symmetry or irreflexivity is bundled into the structure —
`TemporalGraph` carries only `Adj`. Symmetry and looplessness are instead the type classes
`IsSymm` and `IsLoopless`, resolved by instance search wherever a result needs them
(`[G.IsSymm]`, `[G.IsLoopless]`), rather than threaded as explicit hypotheses. Constructions that
preserve one of these properties (`symmetrize`, `fromEdgeSet`, `Subgraph.induce`, …) declare a
matching instance, so resolution finds it automatically, including through several layers of
construction.

There are two notions of edge set. `arcSet`/`arcSize` are the oriented world's: an arc is an
ordered pair of endpoints with a time, and membership characterizes adjacency unconditionally.
`edgeSet`/`size` are the symmetric world's: an edge is an unordered pair (`Sym2 V`) with a time,
and its clean characterization `mem_edgeSet` needs `[G.IsSymm]` (the unconditional
`mem_edgeSet_iff_or` holds regardless, but only as a disjunction of the two orientations).

## Main definitions

* `TemporalGraph.IsSymm`, `TemporalGraph.IsLoopless` : symmetry and looplessness, as classes.
* `TemporalGraph.adjAt` : the time slice `fun x y ↦ G.Adj x y n` of the adjacency at time `n`.
* `TemporalGraph.footprint`, `TemporalGraph.simpleFootprint` : the static footprint, as a
  `Digraph` resp. a `SimpleGraph` (the latter through `SimpleGraph.fromRel`, which symmetrizes
  and drops loops, so it needs no hypothesis).
* `TemporalGraph.IsClique`, `TemporalGraph.IsSimple`, `TemporalGraph.IsProper`,
  `TemporalGraph.IsHappy` : the graph predicates used by Casteigts–Peters–Schoeters and by
  Carnevale–Casteigts–Corsini (see References).
* `TemporalGraph.EarliestEdge`, `TemporalGraph.LatestEdge`, `TemporalGraph.EarliestNeighbor`,
  `TemporalGraph.LatestNeighbor` : the earliest/latest edge and neighbor of a vertex.
* `TemporalGraph.IsSpanningSubgraph`, `TemporalGraph.IsSubgraphOf` : inclusion of temporal graphs
  on the same vertices (it is the order `≤`, with bottom element `⊥` the graph without arcs), resp.
  on two vertex subtypes.
* `TemporalGraph.arcTime` : the time of an arc, as an `Option ℕ`: `some n` for a chosen time `n`
  (unique in a simple graph, `arcTime_eq_some`), `none` when there is no arc.
* `TemporalGraph.arcSet`, `TemporalGraph.edgeSet` : the oriented and symmetric edge sets.
* `TemporalGraph.arcSize`, `TemporalGraph.size` : their `Fintype.card` counts, computable under a
  `Fintype` instance, with `Set.ncard`/`Finset.card` bridge lemmas (`arcSize_eq_ncard`,
  `size_eq_ncard`, `arcSize_eq_card_toFinset`, `size_eq_card_toFinset`).
* `TemporalGraph.neighborSet`, `TemporalGraph.incidenceSet` : the vertex-indexed counting notions,
  inherited by `Subgraph` (see `TemporalGraph.Subgraph` in `Subgraph.lean`).
* `TemporalGraph.symmetrize`, `TemporalGraph.fromArcSet`, `TemporalGraph.fromEdgeSet` : graph
  builders.
* `aesop_temporal_graph` : the `aesop` call using the `TemporalGraph` rule set of `Init.lean`.

## Main results

* `TemporalGraph.IsSimple.mono`, `IsProper.mono`, `IsHappy.mono` : these predicates pass to
  spanning subgraphs (`G ≤ H`).
* `TemporalGraph.symmetrize_le`, `TemporalGraph.le_symmetrize`, `TemporalGraph.symmetrize_eq_self` :
  `G.symmetrize` is the least symmetric graph above `G`, and `G` itself when it is symmetric.
* `TemporalGraph.arcTime_eq_some_iff`, `TemporalGraph.arcTime_comm` : in a simple graph,
  `arcTime u v = some n` exactly when `G.Adj u v n`, and `arcTime` does not depend on the
  orientation when the graph is symmetric; `arcTime_eq_none_iff` : `none` means no arc.
* `TemporalGraph.mem_edgeSet_iff_or` : unconditional characterization of `edgeSet` membership, as
  a disjunction of the two orientations.
* `TemporalGraph.mem_edgeSet` : under `[G.IsSymm]`, `(s(x, y), n) ∈ G.edgeSet ↔ G.Adj x y n`.
* `TemporalGraph.mem_edgeSet_of_arcTime_eq_some` : an edge whose time is given by `arcTime` is an
  edge of the graph.
* `TemporalGraph.size_eq_ncard`, `TemporalGraph.arcSize_eq_ncard` : the counts `size`/`arcSize`
  equal `Set.ncard` of `edgeSet`/`arcSet`.

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025
  (LIPIcs 330, doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321) — the main reference for the
  current development of this library.
* Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse Spanners*, ICALP 2019 / JCSS 2021
  — the original source of the dismountability technique.
-/

@[expose] public section

/-- `aesop_temporal_graph` runs `aesop` with the `TemporalGraph` rule set (declared in `Init.lean`),
at default transparency for introductions and as a terminal tactic (it either closes the goal or
fails). Extra `aesop` clauses are passed through. -/
macro (name := aesop_temporal_graph) "aesop_temporal_graph" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `TemporalGraph):ident]))

universe u

/-- A temporal graph: edges are labeled by the time (ℕ) at which they exist.
No symmetry or irreflexivity is required — see `IsSymm` and `IsLoopless`. -/
@[ext, grind ext, aesop safe constructors (rule_sets := [TemporalGraph])]
structure TemporalGraph (V : Type u) where
  /-- The adjacency labeled by a natural qualifying the time of existence -/
  Adj : V → V → ℕ → Prop


namespace TemporalGraph

variable {V : Type u}

/-- The time-`n` slice of the adjacency, as a binary relation on vertices. It is an `abbrev`, so
`G.adjAt n x y` and `G.Adj x y n` are interchangeable; naming the relation is what lets Mathlib's
API on relations apply: time comes last in `G.Adj x y n`, so the relation is not a subterm of an
adjacency and lemmas with an implicit relation (`Std.Symm.iff`, `comm`, …) cannot infer it. Name
it instead: `comm_of (G.adjAt n)`, `Std.Symm.iff (r := G.adjAt n) x y`, or state the goal with
`adjAt`. -/
abbrev adjAt (G : TemporalGraph V) (n : ℕ) : V → V → Prop := fun x y ↦ G.Adj x y n

/-- Symmetry is a class rather than a plain predicate, so that it is carried by instance
resolution instead of being threaded by hand: constructions that preserve it declare an instance
(see `Subgraph.induce`, `Subgraph.addEdge`, `mount`), and results that need it take `[G.IsSymm]`.
Mirrors the `symm : Std.Symm Adj` field of Mathlib's `SimpleGraph`, time slice by time slice,
without bundling it into the data.

Build it with `IsSymm.of_adj`, and use it through `adj_symm`/`Adj.symm`/`adj_comm` rather than
through the field; the instance `IsSymm.stdSymm` exposes each slice as a `Std.Symm` relation. -/
class IsSymm (G : TemporalGraph V) : Prop where
  symm : ∀ n : ℕ, Std.Symm (G.adjAt n)

/-- Looplessness, as a class; see `IsSymm` for the rationale. -/
class IsLoopless (G : TemporalGraph V) : Prop where
  loopless : ∀ n : ℕ, Std.Irrefl (G.adjAt n)

/-- Each time slice of a symmetric graph is a `Std.Symm` relation, which gives access to Mathlib's
API on symmetric relations (`Std.Symm.iff`, `comm_of`, `symm_of`, `rel_congr`, …). -/
instance IsSymm.stdSymm {G : TemporalGraph V} [hs : G.IsSymm] (n : ℕ) : Std.Symm (G.adjAt n) :=
  hs.symm n

/-- Each time slice of a loopless graph is a `Std.Irrefl` relation. -/
instance IsLoopless.stdIrrefl {G : TemporalGraph V} [hl : G.IsLoopless] (n : ℕ) :
    Std.Irrefl (G.adjAt n) :=
  hl.loopless n

/-- Build `IsSymm` from the unfolded statement `∀ n ⦃x y⦄, G.Adj x y n → G.Adj y x n`, without
nested anonymous constructors. -/
theorem IsSymm.of_adj {G : TemporalGraph V} (h : ∀ n ⦃x y⦄, G.Adj x y n → G.Adj y x n) :
    G.IsSymm :=
  ⟨fun n ↦ ⟨fun _ _ hxy ↦ h n hxy⟩⟩

/-- A loopless graph has no self-adjacency: `¬G.Adj x x n`, at any time `n`. -/
@[simp, grind ., aesop safe (rule_sets := [TemporalGraph])]
protected theorem irrefl {G : TemporalGraph V} [hl : G.IsLoopless] {x : V} {n : ℕ} :
    ¬G.Adj x x n :=
  (hl.loopless n).irrefl x

section Adjacency

variable {G : TemporalGraph V} {x y : V} {n : ℕ}

/-- For a symmetric graph, adjacency is a commutative relation: `G.Adj x y n ↔ G.Adj y x n`. -/
theorem adj_comm [hs : G.IsSymm] (x y : V) (n : ℕ) : G.Adj x y n ↔ G.Adj y x n :=
  (hs.symm n).iff x y

/-- `G.Adj y x n` from `G.Adj x y n`, as a term rather than through the `symm` tactic.
Not `@[symm]`: the `symm` tactic does not synthesize the `[G.IsSymm]` instance argument of a
`@[symm]` lemma, so the kernel would reject the resulting proof (lean4#9997). Use the terms
`h.symm` / `adj_symm h` instead of the tactic. For aesop, symmetry is a `forward` rule: from
`h : G.Adj x y n` it adds `G.Adj y x n` once, where an `apply` rule would loop. -/
@[grind →, aesop safe forward (rule_sets := [TemporalGraph])]
theorem adj_symm [hs : G.IsSymm] (h : G.Adj x y n) : G.Adj y x n :=
  (hs.symm n).symm x y h

/-- Dot-notation form of `adj_symm`: `h.symm` symmetrizes an adjacency proof. -/
theorem Adj.symm [G.IsSymm] (h : G.Adj x y n) : G.Adj y x n :=
  adj_symm h

/-- In a loopless graph, adjacent vertices are distinct. -/
theorem ne_of_adj [G.IsLoopless] (h : G.Adj x y n) : x ≠ y := by grind only [TemporalGraph.irrefl]

/-- Dot-notation form of `ne_of_adj`. -/
@[grind →]
protected theorem Adj.ne [G.IsLoopless] (h : G.Adj x y n) : x ≠ y :=
  G.ne_of_adj h

/-- Symmetric form of `Adj.ne`: `y ≠ x` from `G.Adj x y n` in a loopless graph. -/
@[grind →]
protected theorem Adj.ne' [G.IsLoopless] (h : G.Adj x y n) : y ≠ x :=
  h.ne.symm

end Adjacency

section Definitions

/-- The footprint of a temporal graph `G` is the `Digraph` of its underlying directed edges,
unlabeled by time. -/
def footprint (G : TemporalGraph V) : Digraph V :=
  { Adj := fun x y ↦ ∃ n, G.Adj x y n }

/-- The footprint of `G` as a genuine `SimpleGraph`: distinct vertices `x` and `y` are adjacent
when an arc joins them, in either direction, at some time. This is Mathlib's
`SimpleGraph.fromRel`, which symmetrizes the relation and removes its diagonal, so no symmetry or
looplessness of `G` is needed. -/
def simpleFootprint (G : TemporalGraph V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦ ∃ n, G.Adj x y n

/-- `G` is simple: any two vertices are joined by an arc at no more than one time. -/
@[grind =]
def IsSimple (G : TemporalGraph V) : Prop :=
  ∀ ⦃x y : V⦄ ⦃n m : ℕ⦄, G.Adj x y n → G.Adj x y m → n = m

/-- `S` is a temporal clique of `G`: every two distinct vertices of `S` are joined by an arc at
some time (Mathlib's `SimpleGraph.IsClique`, with time). `G.IsClique Set.univ` is a clique
graph. -/
abbrev IsClique (G : TemporalGraph V) (S : Set V) : Prop :=
  S.Pairwise fun x y ↦ ∃ n, G.Adj x y n

/-- `G.IsClique S` unfolds to pairwise adjacency of `S` in the footprint of `G`, i.e. forgetting
time. -/
lemma isClique_iff_pairwise_footprint_adj {G : TemporalGraph V} {S : Set V} :
    G.IsClique S ↔ S.Pairwise G.footprint.Adj := Iff.rfl

/-- `G` is a temporal clique graph: every two distinct vertices are joined by an arc at some
time. Shorthand for `G.IsClique Set.univ`. On a subgraph `H`, use `H.IsCliqueSubgraph`
instead: the inherited `H.IsCliqueGraph` asks for a clique on all of `V`. -/
abbrev IsCliqueGraph (G : TemporalGraph V) : Prop := G.IsClique Set.univ

/-- `G` is proper: at any given time, a vertex has at most one out-neighbor. -/
@[grind =]
def IsProper (G : TemporalGraph V) : Prop :=
  ∀ ⦃x y z : V⦄ ⦃n : ℕ⦄, G.Adj x y n → G.Adj x z n → y = z

/-- `G` is happy: both simple and proper. -/
def IsHappy (G : TemporalGraph V) : Prop :=
  G.IsSimple ∧ G.IsProper

/-- `G.EarliestEdge x y n`: the arc from `x` to `y` at time `n` is an earliest arc leaving `x`,
i.e. `G.Adj x y n` and no arc leaves `x` before time `n`. -/
@[grind =]
def EarliestEdge (G : TemporalGraph V) (x y : V) (n : ℕ) : Prop :=
  G.Adj x y n ∧ ∀ z : V, ∀ j : ℕ, G.Adj x z j → n ≤ j

/-- `G.LatestEdge x y n`: the arc from `x` to `y` at time `n` is a latest arc leaving `x`,
i.e. `G.Adj x y n` and no arc leaves `x` after time `n`. -/
@[grind =]
def LatestEdge (G : TemporalGraph V) (x y : V) (n : ℕ) : Prop :=
  G.Adj x y n ∧ ∀ z : V, ∀ j : ℕ, G.Adj x z j → j ≤ n

/-- `y` is an earliest neighbor of `x`: some earliest arc leaving `x` ends at `y`. -/
@[grind =]
def EarliestNeighbor (G : TemporalGraph V) (x y : V) : Prop := ∃ n : ℕ, G.EarliestEdge x y n

/-- `y` is a latest neighbor of `x`: some latest arc leaving `x` ends at `y`. -/
@[grind =]
def LatestNeighbor (G : TemporalGraph V) (x y : V) : Prop := ∃ n : ℕ, G.LatestEdge x y n

end Definitions

section Inclusion

variable {Y : Type u}

/-- `G`, carried by the vertices satisfying `P`, is a subgraph of `H`, carried by those
satisfying `P'`: the vertices included, and the adjacencies with them. This is the most general
of the three inclusion relations here — it compares graphs on two different vertex subsets, so it
needs no coercion — and the others are its special cases. -/
@[mk_iff]
structure IsSubgraphOf {P : Y → Prop} {P' : Y → Prop} (G : TemporalGraph {x : Y // P x})
    (H : TemporalGraph {x : Y // P' x}) : Prop where
  incl : ∀ x, P x → P' x
  incl' : ∀ {x y : {x : Y // P x}} {n : ℕ}, G.Adj x y n → H.Adj ⟨_, incl x x.prop⟩
                                                                ⟨_, incl y y.prop⟩
                                                                n

end Inclusion

section Order

/-- `G` is a *spanning* subgraph of `H`: same vertices, fewer adjacencies. This is the relation
behind `≤`. Beware for readers coming from Mathlib: `SimpleGraph.IsSubgraph` names this very
relation, where `SimpleGraph` has no notion of a vertex subset to distinguish it from
`IsSubgraphOf`. -/
def IsSpanningSubgraph (G H : TemporalGraph V) : Prop :=
  ∀ {x y : V} {n : ℕ}, G.Adj x y n → H.Adj x y n

instance : LE (TemporalGraph V) :=
  ⟨IsSpanningSubgraph⟩

/-- `G ≤ H` unfolds to pointwise adjacency implication: every arc of `G` is an arc of `H`. -/
@[grind =]
lemma le_iff_adj {G H : TemporalGraph V} :
    G ≤ H ↔ ∀ x y : V, ∀ n : ℕ, G.Adj x y n → H.Adj x y n :=
  .rfl

/-- `IsSpanningSubgraph` is definitionally the `≤` order on `TemporalGraph`. -/
@[simp]
theorem isSpanningSubgraph_eq_le :
    (IsSpanningSubgraph : TemporalGraph V → TemporalGraph V → Prop) =
    (· ≤ ·) :=
  rfl

instance : Bot (TemporalGraph V) where
  bot := { Adj _ _ _ := False }

end Order

section Monotonicity

/-- A spanning subgraph of a simple graph is simple. -/
theorem IsSimple.mono {G H : TemporalGraph V} (h₀ : H.IsSimple) (h₁ : G ≤ H) : G.IsSimple :=
  fun _ _ _ _ hn hm ↦ h₀ (h₁ hn) (h₁ hm)

/-- A spanning subgraph of a proper graph is proper. -/
theorem IsProper.mono {G H : TemporalGraph V} (h₀ : H.IsProper) (h₁ : G ≤ H) : G.IsProper :=
  fun _ _ _ _ hy hz ↦ h₀ (h₁ hy) (h₁ hz)

/-- A spanning subgraph of a happy graph is happy. -/
theorem IsHappy.mono {G H : TemporalGraph V} (h₀ : H.IsHappy) (h₁ : G ≤ H) : G.IsHappy :=
  ⟨h₀.1.mono h₁, h₀.2.mono h₁⟩

end Monotonicity

section ArcTime

/-- The time of the arc from `u` to `v`: `some n` for a time `n` with `G.Adj u v n` (unique in a
simple graph: `arcTime_eq_some`), and `none` when there is no such arc. In a symmetric simple graph
it does not depend on the orientation (`arcTime_comm`): it is then the label `λ({u, v})` of the
edge.

To use the time as a number, first prove that the arc exists, then unwrap:
`(G.arcTime u v).get (arcTime_isSome_iff.2 h)` with `h : ∃ n, G.Adj u v n`. There is no default
value: `Option.get!` and `Option.getD` would bring back a junk time indistinguishable from a real
one. Do not compare these values with the order of `Option` either, in which `none` is the least
element (`none ≤ some τ` holds): state a comparison through the value,
`∃ n ∈ G.arcTime u v, n ≤ τ`, which is false on `none`. -/
noncomputable def arcTime (G : TemporalGraph V) (u v : V) : Option ℕ := by
  classical
  exact if h : ∃ n, G.Adj u v n then some h.choose else none

variable {G : TemporalGraph V} {u v w w' : V} {n m : ℕ}

/-- An arc exists exactly when its time is defined. -/
theorem arcTime_isSome_iff : (G.arcTime u v).isSome ↔ ∃ n, G.Adj u v n := by
  unfold arcTime
  split_ifs with h <;> simp [h]

/-- The time of an arc is `none` exactly when there is no arc. -/
theorem arcTime_eq_none_iff : G.arcTime u v = none ↔ ∀ n, ¬G.Adj u v n := by
  rw [← Option.not_isSome_iff_eq_none, arcTime_isSome_iff, not_exists]

/-- The arc exists at the time given by `arcTime`. -/
theorem adj_of_arcTime_eq_some (h₀ : G.arcTime u v = some n) : G.Adj u v n := by
  unfold arcTime at h₀
  split_ifs at h₀ with h₁
  exact Option.some_injective _ h₀ ▸ h₁.choose_spec

/-- In a simple graph, `arcTime u v` is the time of any arc from `u` to `v`. -/
@[grind →]
theorem arcTime_eq_some (h₀ : G.IsSimple) (h₁ : G.Adj u v n) : G.arcTime u v = some n := by
  obtain ⟨m, h₂⟩ := Option.isSome_iff_exists.1 (arcTime_isSome_iff.2 ⟨n, h₁⟩)
  -- the chosen time `m` and `n` are two times of the same arc
  rw [h₂, h₀ (adj_of_arcTime_eq_some h₂) h₁]

/-- In a simple graph, `arcTime` characterizes the arcs. -/
theorem arcTime_eq_some_iff (h₀ : G.IsSimple) : G.arcTime u v = some n ↔ G.Adj u v n :=
  ⟨adj_of_arcTime_eq_some, arcTime_eq_some h₀⟩

/-- In a symmetric simple graph, `arcTime` does not depend on the orientation. -/
theorem arcTime_comm [G.IsSymm] (h₀ : G.IsSimple) (u v : V) : G.arcTime u v = G.arcTime v u := by
  cases h₁ : G.arcTime u v with
  | none =>
    -- no arc in either orientation
    exact (arcTime_eq_none_iff.2 fun n h ↦ arcTime_eq_none_iff.1 h₁ n h.symm).symm
  | some n => exact (arcTime_eq_some h₀ (adj_of_arcTime_eq_some h₁).symm).symm

/-- In a proper graph, two arcs leaving `v` at the same time have the same endpoint: the times of
the arcs leaving `v` are pairwise distinct. -/
theorem eq_of_arcTime_eq_some (h₀ : G.IsProper) (h₁ : G.arcTime v w = some n)
    (h₂ : G.arcTime v w' = some n) : w = w' :=
  h₀ (adj_of_arcTime_eq_some h₁) (adj_of_arcTime_eq_some h₂)

/-- Passing to a supergraph keeps the time of an arc, when the supergraph is simple. -/
theorem arcTime_eq_some_of_le {G' : TemporalGraph V} (h₀ : G ≤ G') (h₁ : G'.IsSimple)
    (h₂ : G.arcTime u v = some n) : G'.arcTime u v = some n :=
  arcTime_eq_some h₁ (h₀ (adj_of_arcTime_eq_some h₂))

/-- In a simple graph, an earliest edge happens at the `arcTime` of its arc. -/
theorem EarliestEdge.arcTime_eq_some (h₀ : G.IsSimple) (h₁ : G.EarliestEdge u v n) :
    G.arcTime u v = some n :=
  TemporalGraph.arcTime_eq_some h₀ h₁.1

/-- In a simple graph, a latest edge happens at the `arcTime` of its arc. -/
theorem LatestEdge.arcTime_eq_some (h₀ : G.IsSimple) (h₁ : G.LatestEdge u v n) :
    G.arcTime u v = some n :=
  TemporalGraph.arcTime_eq_some h₀ h₁.1

end ArcTime

section NeighborSet

/-- The set of out-neighbors of `x` in `G`, forgetting time. -/
def neighborSet (G : TemporalGraph V) (x : V) := {y | ∃ n : ℕ, G.Adj x y n}

/-- `y ∈ G.neighborSet x` iff `x` is adjacent to `y` at some time. -/
@[simp]
theorem mem_neighborSet (G : TemporalGraph V) (x y : V) :
    y ∈ G.neighborSet x ↔ ∃ n : ℕ, G.Adj x y n :=
  Iff.rfl

end NeighborSet

section IncidenceSet

/-- The edges incident to `x`: pairs `(y, n)` such that `x` is adjacent to `y` at time `n`. -/
def incidenceSet (G : TemporalGraph V) (x : V) : Set (V × ℕ) :=
  { (y, n) : V × ℕ | G.Adj x y n }

end IncidenceSet

section ArcSet

/-- The *arcs* of `G`: oriented edges, as an ordered pair of endpoints with their time. This is
the oriented world's notion, and it characterizes adjacency with no hypothesis at all — unlike
`edgeSet`, which lives on `Sym2 V` and therefore only does so for a symmetric graph
(`mem_edgeSet`). -/
def arcSet (G : TemporalGraph V) : Set (V × V × ℕ) :=
  {a | G.Adj a.1 a.2.1 a.2.2}

/-- `(x, y, n)` is an arc of `G` iff `G.Adj x y n`. -/
@[simp]
theorem mem_arcSet (G : TemporalGraph V) {x y : V} {n : ℕ} :
    (x, y, n) ∈ G.arcSet ↔ G.Adj x y n :=
  Iff.rfl

/-- Build a temporal graph from a set of arcs. Oriented: nothing is assumed, and nothing is
symmetrized — see `fromEdgeSet` for the symmetric counterpart. -/
def fromArcSet (s : Set (V × V × ℕ)) : TemporalGraph V where
  Adj x y n := (x, y, n) ∈ s

/-- `(fromArcSet s).Adj x y n` iff `(x, y, n) ∈ s`. -/
@[simp]
theorem fromArcSet_adj {s : Set (V × V × ℕ)} {x y : V} {n : ℕ} :
    (fromArcSet s).Adj x y n ↔ (x, y, n) ∈ s :=
  Iff.rfl

/-- `fromArcSet` and `arcSet` are mutually inverse: `(fromArcSet s).arcSet = s`. -/
@[simp]
theorem arcSet_fromArcSet (s : Set (V × V × ℕ)) : (fromArcSet (V := V) s).arcSet = s := by
  ext ⟨x, y, n⟩
  rfl

end ArcSet

section EdgeSet

/-- The unordered edges of `G`, with their time: a pair `(p, n)` belongs when `p` is the
unordered pair of the endpoints of an arc at time `n`. Note that this asks `p` to *be* such a
pair, not merely to have its endpoints among them: quantifying over the members of `p` would
also admit `s(x, y)` whenever `G` has a loop at `x`. -/
def edgeSet (G : TemporalGraph V) : Set (Sym2 V × ℕ) :=
  {(p, n) | ∃ x y, p = s(x, y) ∧ G.Adj x y n}

/-- Membership in `edgeSet`, with no hypothesis: an unordered pair carries an edge exactly when
one of its two orientations is an arc. For a symmetric graph the two disjuncts collapse — see
`mem_edgeSet`. -/
theorem mem_edgeSet_iff_or (G : TemporalGraph V) {x y : V} {n : ℕ} :
    (s(x, y), n) ∈ G.edgeSet ↔ G.Adj x y n ∨ G.Adj y x n := by
  constructor
  · rintro ⟨a, b, hp, hadj⟩
    -- `s(x, y) = s(a, b)` leaves the two orientations of the pair
    rcases Sym2.eq_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hadj
    · exact Or.inr hadj
  · rintro (h | h)
    · exact ⟨x, y, rfl, h⟩
    · exact ⟨y, x, Sym2.eq_swap, h⟩

/-- For a symmetric graph, `(s(x, y), n) ∈ G.edgeSet` iff `G.Adj x y n`. -/
@[simp, grind =]
theorem mem_edgeSet (G : TemporalGraph V) [G.IsSymm] {x y : V} {n : ℕ} :
    (s(x, y), n) ∈ G.edgeSet ↔ G.Adj x y n := by
  rw [mem_edgeSet_iff_or]
  exact or_iff_left_iff_imp.mpr fun h ↦ h.symm

/-- An edge whose time is given by `arcTime` is an edge of the graph. -/
theorem mem_edgeSet_of_arcTime_eq_some {G : TemporalGraph V} {u v : V} {n : ℕ}
    (h₀ : G.arcTime u v = some n) : (s(u, v), n) ∈ G.edgeSet :=
  ⟨u, v, rfl, adj_of_arcTime_eq_some h₀⟩

end EdgeSet

section Size

/-- The number of unordered edges: the symmetric world's measure. Computable, under a
`Fintype` instance on the edge set; `size_eq_ncard` gives the instance-free `Set.ncard` form, in
which the counting lemmas of the library are stated. -/
def size (G : TemporalGraph V) [Fintype G.edgeSet] : ℕ := Fintype.card G.edgeSet

/-- The number of arcs: the oriented counterpart of `size`. Computable, under a `Fintype`
instance on the arc set; `arcSize_eq_ncard` gives the instance-free `Set.ncard` form. -/
def arcSize (G : TemporalGraph V) [Fintype G.arcSet] : ℕ := Fintype.card G.arcSet

/-- `size` is `Set.ncard` of the edge set: the instance-free form, in which the counting
lemmas of the library (`ncard_edgeSet_addEdge_le`, …) are stated. -/
theorem size_eq_ncard (G : TemporalGraph V) [Fintype G.edgeSet] :
    G.size = G.edgeSet.ncard :=
  Set.fintypeCard_eq_ncard G.edgeSet

/-- `arcSize` is `Set.ncard` of the arc set: the instance-free counterpart of `size_eq_ncard`. -/
theorem arcSize_eq_ncard (G : TemporalGraph V) [Fintype G.arcSet] :
    G.arcSize = G.arcSet.ncard :=
  Set.fintypeCard_eq_ncard G.arcSet

/-- `size` is also the `Finset.card` of the edge set's `toFinset`. -/
theorem size_eq_card_toFinset (G : TemporalGraph V) [Fintype G.edgeSet] :
    G.size = G.edgeSet.toFinset.card :=
  (Set.toFinset_card G.edgeSet).symm

/-- `arcSize` is also the `Finset.card` of the arc set's `toFinset`. -/
theorem arcSize_eq_card_toFinset (G : TemporalGraph V) [Fintype G.arcSet] :
    G.arcSize = G.arcSet.toFinset.card :=
  (Set.toFinset_card G.arcSet).symm

end Size

section Symmetrize

variable {G : TemporalGraph V}

/-- The *symmetrization* of `G`: an arc in either direction becomes an edge in both. It is the
smallest symmetric temporal graph above `G`. -/
def symmetrize (G : TemporalGraph V) : TemporalGraph V where
  Adj x y n := G.Adj x y n ∨ G.Adj y x n

/-- `G.symmetrize.Adj x y n` iff `G.Adj x y n ∨ G.Adj y x n`. -/
@[simp]
theorem symmetrize_adj {x y : V} {n : ℕ} :
    G.symmetrize.Adj x y n ↔ G.Adj x y n ∨ G.Adj y x n :=
  Iff.rfl

/-- The symmetrization of a temporal graph is symmetric. -/
instance symmetrize_isSymm (G : TemporalGraph V) : G.symmetrize.IsSymm :=
  .of_adj fun _ _ _ h ↦ Or.symm h

/-- Symmetrizing adds no loop, so it preserves looplessness. -/
instance symmetrize_isLoopless (G : TemporalGraph V) [G.IsLoopless] : G.symmetrize.IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ Or.elim h (fun h ↦ G.irrefl h) fun h ↦ G.irrefl h⟩⟩

/-- `G` is a spanning subgraph of its own symmetrization. -/
theorem le_symmetrize (G : TemporalGraph V) : G ≤ G.symmetrize := fun h ↦ Or.inl h

/-- A symmetric graph is its own symmetrization. -/
theorem symmetrize_eq_self (G : TemporalGraph V) [G.IsSymm] : G.symmetrize = G := by
  ext x y n
  exact ⟨fun h ↦ Or.elim h id fun h ↦ h.symm, Or.inl⟩

/-- `G.symmetrize` is the least symmetric graph above `G`. -/
theorem symmetrize_le {H : TemporalGraph V} [H.IsSymm] (h : G ≤ H) : G.symmetrize ≤ H :=
  fun hadj ↦ Or.elim hadj (fun hadj ↦ h hadj) fun hadj ↦ (h hadj).symm

end Symmetrize

section FromEdgeSet

/-- Build a temporal graph from a set of unordered edges. Symmetric by construction: an
unordered pair is read in both directions. -/
def fromEdgeSet (s : Set (Sym2 V × ℕ)) : TemporalGraph V where
  Adj x y n := (s(x, y), n) ∈ s

/-- `(fromEdgeSet s).Adj x y n` iff `(s(x, y), n) ∈ s`. -/
@[simp]
theorem fromEdgeSet_adj {s : Set (Sym2 V × ℕ)} {x y : V} {n : ℕ} :
    (fromEdgeSet s).Adj x y n ↔ (s(x, y), n) ∈ s :=
  Iff.rfl

/-- A graph built from a set of unordered edges is symmetric. -/
instance fromEdgeSet_isSymm (s : Set (Sym2 V × ℕ)) : (fromEdgeSet (V := V) s).IsSymm :=
  .of_adj fun _ _ _ h ↦ by simpa [Sym2.eq_swap] using h

/-- `fromEdgeSet` and `edgeSet` are mutually inverse: `(fromEdgeSet s).edgeSet = s`. -/
@[simp]
theorem edgeSet_fromEdgeSet (s : Set (Sym2 V × ℕ)) : (fromEdgeSet (V := V) s).edgeSet = s := by
  ext ⟨p, n⟩
  induction p using Sym2.ind with
  | _ x y => simp

end FromEdgeSet

end TemporalGraph
