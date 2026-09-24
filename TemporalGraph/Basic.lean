/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Init
import Mathlib

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
* `TemporalGraph.IsClique`, `TemporalGraph.IsSimple`, `TemporalGraph.IsProper`,
  `TemporalGraph.IsHappy` : the graph predicates from Casteigts–Peters–Schoeters.
* `TemporalGraph.EarliestEdge`, `TemporalGraph.LatestEdge`, `TemporalGraph.EarliestNeighbor`,
  `TemporalGraph.LatestNeighbor` : the earliest/latest edge and neighbor of a vertex.
* `TemporalGraph.arcSet`, `TemporalGraph.edgeSet` : the oriented and symmetric edge sets.
* `TemporalGraph.symmetrize`, `TemporalGraph.fromArcSet`, `TemporalGraph.fromEdgeSet` : graph
  builders.

## References

* Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse Spanners*, ICALP 2019 / JCSS.
-/

macro (name := aesop_temporal_graph) "aesop_temporal_graph" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `TemporalGraph):ident]))



universe u

/-- A temporal graph: edges are labeled by the time (ℕ) at which they exist.
No symmetry or irreflexivity is required — see `IsSymm` and `IsLoopless`. -/
@[ext, aesop safe constructors (rule_sets := [TemporalGraph])]
structure TemporalGraph (V : Type u) where
  /-- The adjacency labeled by a natural qualifying the time of existence -/
  Adj : V → V → ℕ → Prop



namespace TemporalGraph

variable {V : Type u}

/-- Symmetry is a class rather than a plain predicate, so that it is carried by instance
resolution instead of being threaded by hand: constructions that preserve it declare an instance
(see `Subgraph.induce`, `addEdgeSymm`, `mount`), and results that need it take `[G.IsSymm]`.
Mirrors the `symm` field of Mathlib's `SimpleGraph`, without bundling it into the data. -/
class IsSymm (G : TemporalGraph V) : Prop where
  symm : ∀ n : ℕ, Symmetric (fun x y => G.Adj x y n)

/-- Looplessness, as a class; see `IsSymm` for the rationale. -/
class IsLoopless (G : TemporalGraph V) : Prop where
  loopless : ∀ n : ℕ, Std.Irrefl (fun x y => G.Adj x y n)

@[simp, aesop safe (rule_sets := [TemporalGraph])]
protected theorem irrefl {G : TemporalGraph V} [hl : G.IsLoopless] {x : V} {n : ℕ} :
    ¬G.Adj x x n :=
  (hl.loopless n).irrefl x

section Adjacency

variable {G : TemporalGraph V} {x y : V} {n : ℕ}

theorem adj_comm [hs : G.IsSymm] (x y : V) (n : ℕ) : G.Adj x y n ↔ G.Adj y x n :=
  ⟨fun h => hs.symm n h, fun h => hs.symm n h⟩

@[symm]
theorem adj_symm [hs : G.IsSymm] (h : G.Adj x y n) : G.Adj y x n :=
  hs.symm n h

theorem Adj.symm [hs : G.IsSymm] (h : G.Adj x y n) : G.Adj y x n :=
  hs.symm n h

theorem ne_of_adj [G.IsLoopless] (h : G.Adj x y n) : x ≠ y := by
  rintro rfl
  exact G.irrefl h

protected theorem Adj.ne [G.IsLoopless] (h : G.Adj x y n) : x ≠ y :=
  G.ne_of_adj h

protected theorem Adj.ne' [G.IsLoopless] (h : G.Adj x y n) : y ≠ x :=
  h.ne.symm

end Adjacency

section Definitions

/-- The footprint of a TemporalGraph is a Digraph representing the underlying
directed edges unlabelled by time. -/
def footprint (G : TemporalGraph V) : Digraph V :=
  { Adj := fun x y => ∃ n, G.Adj x y n }

def IsSimple (G : TemporalGraph V) : Prop :=
  ∀ (x y : V) (n m : ℕ), G.Adj x y n ∧ G.Adj x y m → n=m

def IsClique (G : TemporalGraph V) : Prop :=
  ∀ x y : V, x ≠ y → ∃ t, G.Adj x y t

lemma isClique_iff_footprint_isComplete {G : TemporalGraph V} :
    G.IsClique ↔ Set.univ.Pairwise G.footprint.Adj := by
  simp only [IsClique, ne_eq, Set.Pairwise, Set.mem_univ, footprint, forall_const]

def IsProper (G : TemporalGraph V) : Prop :=
  ∀ x y z : V, ∀ n : ℕ, G.Adj x y n ∧ G.Adj x z n → y = z

def IsHappy (G : TemporalGraph V) : Prop :=
  G.IsSimple ∧ G.IsProper

/-- The *earliest edge* of *x*, with *y* destination at *n* -/
def EarliestEdge (G : TemporalGraph V) (x y : V) (n : ℕ) : Prop :=
  G.Adj x y n ∧ ∀ z : V, ∀ j : ℕ, G.Adj x z j → n ≤ j

/-- The *latest edge* of *x*, with *y* destination at *n* -/
def LatestEdge (G : TemporalGraph V) (x y : V) (n : ℕ) : Prop :=
  G.Adj x y n ∧ ∀ z : V, ∀ j : ℕ, G.Adj x z j → j ≤ n

/-- *y* is an *earliest neighbor* of *x* -/
def EarliestNeighbor (G : TemporalGraph V) (x y : V) : Prop := ∃ n : ℕ, G.EarliestEdge x y n

/-- *y* is a *latest neighbor* of *x* -/
def LatestNeighbor (G : TemporalGraph V) (x y : V) : Prop := ∃ n : ℕ, G.LatestEdge x y n

end Definitions

section Inclusion

variable {X Y : Type u}

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

instance : Coe (TemporalGraph V) (TemporalGraph {x : V // True}) where
  coe G := ⟨fun x y n => G.Adj x y n⟩

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

lemma le_iff_adj {G H : TemporalGraph V} :
    G ≤ H ↔ ∀ x y : V, ∀ n : ℕ, G.Adj x y n → H.Adj x y n :=
  .rfl

@[simp]
theorem isSpanningSubgraph_eq_le :
    (IsSpanningSubgraph : TemporalGraph V -> TemporalGraph V -> Prop) =
    (· ≤ ·) :=
  rfl

instance : Bot (TemporalGraph V) where
  bot := { Adj _ _ _ := False }

end Order

section neighborSet


def neighborSet (G : TemporalGraph V) (x : V) := {y | ∃ n : ℕ, G.Adj x y n}

@[simp]
theorem mem_neighborSet (G : TemporalGraph V) (x y : V) :
    y ∈ G.neighborSet x ↔ ∃ n : ℕ, G.Adj x y n :=
  Iff.rfl

end neighborSet

section arcSet

/-- The *arcs* of `G`: oriented edges, as an ordered pair of endpoints with their time. This is
the oriented world's notion, and it characterizes adjacency with no hypothesis at all — unlike
`edgeSet`, which lives on `Sym2 V` and therefore only does so for a symmetric, loopless graph. -/
def arcSet (G : TemporalGraph V) : Set (V × V × ℕ) :=
  {a | G.Adj a.1 a.2.1 a.2.2}

@[simp]
theorem mem_arcSet (G : TemporalGraph V) {x y : V} {n : ℕ} :
    (x, y, n) ∈ G.arcSet ↔ G.Adj x y n :=
  Iff.rfl

/-- Build a temporal graph from a set of arcs. Oriented: nothing is assumed, and nothing is
symmetrized — see `fromEdgeSet` for the symmetric counterpart. -/
def fromArcSet (s : Set (V × V × ℕ)) : TemporalGraph V where
  Adj x y n := (x, y, n) ∈ s

@[simp]
theorem fromArcSet_adj {s : Set (V × V × ℕ)} {x y : V} {n : ℕ} :
    (fromArcSet s).Adj x y n ↔ (x, y, n) ∈ s :=
  Iff.rfl

@[simp]
theorem arcSet_fromArcSet (s : Set (V × V × ℕ)) : (fromArcSet (V := V) s).arcSet = s := by
  ext ⟨x, y, n⟩
  rfl

end arcSet

section edgeSet

/-- The unordered edges of `G`, with their time: a pair `(p, n)` belongs when `p` is the
unordered pair of the endpoints of an arc at time `n`. Note that this asks `p` to *be* such a
pair, not merely to have its endpoints among them — quantifying over the members of `p` would
also admit `s(x, y)` whenever `G` has a loop at `x`, which is why a looplessness hypothesis used
to be needed to use this set at all. -/
def edgeSet (G : TemporalGraph V) : Set ((Sym2 V) × ℕ) :=
  {(p, n) | ∃ x y, p = s(x,y) ∧ G.Adj x y n}

/-- Membership in `edgeSet`, with no hypothesis: an unordered pair carries an edge exactly when
one of its two orientations is an arc. For a symmetric graph the two disjuncts collapse — see
`mem_edgeSet`. -/
theorem mem_edgeSet_iff_or (G : TemporalGraph V) {x y : V} {n : ℕ} :
    (s(x,y), n) ∈ G.edgeSet ↔ G.Adj x y n ∨ G.Adj y x n := by
  constructor
  · rintro ⟨a, b, hp, hadj⟩
    rcases Sym2.eq_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hadj
    · exact Or.inr hadj
  · rintro (h | h)
    · exact ⟨x, y, rfl, h⟩
    · exact ⟨y, x, Sym2.eq_swap, h⟩

@[simp]
theorem mem_edgeSet (G : TemporalGraph V) [G.IsSymm] {x y : V} {n : ℕ} :
    (s(x,y), n) ∈ G.edgeSet ↔ G.Adj x y n := by
  rw [mem_edgeSet_iff_or]
  exact or_iff_left_iff_imp.mpr fun h ↦ h.symm

end edgeSet

section Size

/-- The number of unordered edges: the symmetric world's measure. -/
def size (G : TemporalGraph V) [Fintype G.edgeSet] := Fintype.card G.edgeSet

/-- The number of arcs: the oriented counterpart of `size`. -/
def arcSize (G : TemporalGraph V) [Fintype G.arcSet] := Fintype.card G.arcSet

end Size

section Symmetrize

variable {G : TemporalGraph V}

/-- The *symmetrization* of `G`: an arc in either direction becomes an edge in both. It is the
smallest symmetric temporal graph above `G`. -/
def symmetrize (G : TemporalGraph V) : TemporalGraph V where
  Adj x y n := G.Adj x y n ∨ G.Adj y x n

@[simp]
theorem symmetrize_adj {x y : V} {n : ℕ} :
    G.symmetrize.Adj x y n ↔ G.Adj x y n ∨ G.Adj y x n :=
  Iff.rfl

instance symmetrize_isSymm (G : TemporalGraph V) : G.symmetrize.IsSymm :=
  ⟨fun _ _ _ h ↦ Or.symm h⟩

/-- Symmetrizing adds no loop, so it preserves looplessness. -/
instance symmetrize_isLoopless (G : TemporalGraph V) [G.IsLoopless] : G.symmetrize.IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ Or.elim h (fun h ↦ G.irrefl h) fun h ↦ G.irrefl h⟩⟩

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
def fromEdgeSet (s : Set ((Sym2 V) × ℕ)) : TemporalGraph V where
  Adj x y n := (s(x,y), n) ∈ s

@[simp]
theorem fromEdgeSet_adj {s : Set ((Sym2 V) × ℕ)} {x y : V} {n : ℕ} :
    (fromEdgeSet s).Adj x y n ↔ (s(x,y), n) ∈ s :=
  Iff.rfl

instance fromEdgeSet_isSymm (s : Set ((Sym2 V) × ℕ)) : (fromEdgeSet (V := V) s).IsSymm :=
  ⟨fun _ _ _ h ↦ by simpa [Sym2.eq_swap] using h⟩

@[simp]
theorem edgeSet_fromEdgeSet (s : Set ((Sym2 V) × ℕ)) : (fromEdgeSet (V := V) s).edgeSet = s := by
  ext ⟨p, n⟩
  induction p using Sym2.ind with
  | _ x y => simp

end FromEdgeSet

end TemporalGraph
