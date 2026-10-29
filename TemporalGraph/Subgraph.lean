/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Basic
public import TemporalGraph.TemporalWalk

import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Set.Finite.Lattice

/-!
# Sub-temporal-graphs

A subgraph of a temporal graph is a set of vertices together with a temporal adjacency relation
that refines the ambient graph's and whose edges have both endpoints in that vertex set. Unlike
Mathlib's `SimpleGraph.Subgraph`, symmetry is not a field: a subgraph may be oriented, and the
symmetric world is entered by assuming `[H.IsSymm]`.

This file defines `TemporalGraph.Subgraph`, its bounded order, the constructions that build one,
and the subgraph counterparts of the vertex- and edge-indexed notions of `TemporalGraph.Basic`.

## Main definitions

* `Subgraph G` : the type of subgraphs of `G : TemporalGraph V`.
* `Subgraph.coe` : the view of `H : Subgraph G` as a `TemporalGraph H.verts`, with the bridge
  lemmas `isSymm_iff_coe`, `isSimple_iff_coe`, `isProper_iff_coe`, `isHappy_iff_coe`,
  `isClique_iff_coe`, `coe_earliestEdge`, `coe_latestEdge`.
* `Subgraph.IsSpanning`, `Subgraph.IsInduced` : `H` carries all of `V`, resp. all the arcs of `G`
  between its own vertices.
* `Subgraph.IsCliqueSubgraph` : `H.IsClique H.verts`. `IsClique` needs no `Subgraph` duplicate,
  since it takes a vertex set as an argument.
* `Subgraph.IsMatching`, `Subgraph.IsPerfectMatching`, `Subgraph.IsPerfectMatchingOf` : matchings,
  quantifying over `H.verts`.
* `Subgraph.order` : the number of vertices of `H`. The edge-indexed notions `neighborSet`,
  `incidenceSet`, `edgeSet` and `size` are inherited from `TemporalGraph`.
* `Subgraph.induce`, `Subgraph.deleteVerts`, `Subgraph.addVerts` : restricting or enlarging the
  vertex set.
* `Subgraph.addArc`, `Subgraph.addEdge` : adding one orientation of an edge (no symmetry needed),
  resp. both orientations (needs `[G.IsSymm]`).
* `Subgraph.footprintEdgeSet`, `Subgraph.edgeSetToFootprintEdgeSet` : the edges of `H` with the
  times forgotten, and the map onto them.
* `TemporalGraph.toSubgraph`, `Subgraph.fromEdgeSet` : the subgraph given by a temporal graph below
  `G`, resp. by a set of edges.

## Main results

* Coe bridge: the instances `Subgraph.coe_isSymm`, `Subgraph.coe_isLoopless` and the lemmas above.
* Order: `BoundedOrder`, `PartialOrder` and `SemilatticeSup` instances on `Subgraph G`, with `⊤`
  the whole of `G`, `⊥` the empty subgraph and `⊔` the union of vertex sets and arcs; `le_def`,
  `lt_iff`, `toTemporalGraph_le`, `toTemporalGraph_le_self`.
* Induce, delete, add: `induce_le_of_subset`, `deleteVerts_le`, `addVerts_le`, `addArc_le`,
  `addEdge_le`, `addArc_le_addEdge`.
* Earliest and latest edges: `earliestEdge_exists_of_nonempty_finite_incidenceSet` and its
  `latest` counterpart, `earliestEdge_lt_of_proper`.
* Edge set: `edgeSet_mono`, `edgeSet_subset`, `sup_edgeSet`, `addEdge_edgeSet`,
  `le_iff_edgeSet_and_verts`, and `edgeSetToFootprintEdgeSet_bijective` (for a symmetric, simple
  subgraph, edges and footprint edges are in bijection).
* Finiteness: `finite_edgeSet_of_finite_simple`, `deleteVerts_finite`, `finite_induce_verts`.
* Size: the `Set.ncard` forms `ncard_edgeSet_of_simple`, `ncard_edgeSet_addEdge`,
  `ncard_edgeSet_addEdge_le`, `ncard_edgeSet_addVerts`, `order_eq_ncard`, free of `Fintype`
  hypotheses, and their `size` counterparts.
* `Subgraph.fromEdgeSet_eq`, `fromEdgeSet_le`, `fromEdgeSet_mono`, `adj_of_fromEdgeSet_le` : the
  subgraph built from a set of edges of `H` lies in `H`, and grows with the set.
* `Subgraph.exists_matchingEdges` : a family of unique partners `a ↦ (v, n)` over a finite set `A`
  yields a set of at most `|A|` edges `(s(v, a), n)`.

## Implementation notes

* `Subgraph` **extends** `TemporalGraph V`: a subgraph literally *is* a temporal graph together
  with a vertex set and compatibility proofs. The parent's whole lemma corpus therefore applies to
  `H.Adj` for free, and notions such as `H.IsSymm`, `H.IsSimple`, `H.EarliestEdge` or `H.edgeSet`
  resolve through generalized field notation to the `TemporalGraph` ones taken at
  `H.toTemporalGraph`, instead of being redefined here. Only the notions quantifying over
  `H.verts` are defined afresh.
* The flip side of that inheritance: since `H.Adj x y n` *is* the parent's `Adj`, dot notation on
  a proof `h : H.Adj x y n` resolves in the `TemporalGraph.Adj` namespace, never in
  `TemporalGraph.Subgraph.Adj`. The subgraph-specific helpers must accordingly be written with the
  subgraph in front — `H.adj_sub h`, `H.edge_vert h`, `H.edge_vert' h`, `H.adj_symm h` — and not
  as `h.adj_sub`, `h.fst_mem`, `h.snd_mem`, `h.symm`. The fully qualified spellings, such as
  `TemporalGraph.Subgraph.Adj.snd_mem h`, keep working.
-/

@[expose] public section

universe u

namespace TemporalGraph

/-- A subgraph of the temporal graph `G`: a temporal graph (the inherited adjacency `Adj`) together
with a vertex set `verts`, whose adjacency is contained in that of `G` and whose arcs have both
endpoints in `verts`. The structure is unbundled: it carries no symmetry or looplessness field
(these are the classes `IsSymm`/`IsLoopless`), so a subgraph may be oriented. -/
@[ext]
structure Subgraph {V : Type u} (G : TemporalGraph V) extends TemporalGraph V where
  /-- The vertex set of the subgraph. -/
  verts : Set V
  /-- Every arc of the subgraph is an arc of `G`, at the same time. -/
  adj_sub : ∀ {x y : V} {n : ℕ}, Adj x y n → G.Adj x y n
  /-- The tail of every arc of the subgraph is a vertex of the subgraph. -/
  edge_vert : ∀ {x y : V} {n : ℕ}, Adj x y n → x ∈ verts
  /-- The head of every arc of the subgraph is a vertex of the subgraph. This field replaces
  symmetry: without it, `edge_vert` alone would not control the head of an oriented arc. -/
  edge_vert' : ∀ {x y : V} {n : ℕ}, Adj x y n → y ∈ verts

namespace Subgraph

variable {V : Type u} {G : TemporalGraph V}

section CoeAdjacency

/-- A subgraph of a loopless graph is loopless: an instance, so that `[G.IsLoopless]` alone
suffices at every use site, however deeply the subgraph is built up. -/
instance loopless (H : Subgraph G) [G.IsLoopless] : H.IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩⟩

/-- No vertex of a subgraph of a loopless graph is adjacent to itself, at any time. -/
@[simp, grind ., aesop safe (rule_sets := [TemporalGraph])]
protected theorem irrefl {H : Subgraph G} [G.IsLoopless] {x : V} {n : ℕ} :
    ¬H.Adj x x n :=
  TemporalGraph.irrefl

/-- In a symmetric subgraph, `H.Adj x y n` and `H.Adj y x n` are equivalent. -/
theorem adj_comm (H : Subgraph G) [H.IsSymm] (x y : V) (n : ℕ) :
    H.Adj x y n ↔ H.Adj y x n :=
  TemporalGraph.adj_comm x y n

/-- Adjacency is symmetric in a symmetric subgraph: `H.Adj x y n` gives `H.Adj y x n`. It carries
no attribute: symmetry is handled once, on `TemporalGraph.adj_symm` (see `Basic.lean`), which
applies to `H.Adj` since it *is* `H.toTemporalGraph.Adj`. -/
theorem adj_symm (H : Subgraph G) [H.IsSymm] {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.Adj y x n :=
  TemporalGraph.adj_symm h

/-- Dot-notation form of `adj_symm`. It carries no aesop or `symm` attribute: as a `safe` apply
rule it makes aesop loop (see `TemporalGraph.adj_symm`). -/
protected theorem Adj.symm {H : Subgraph G} [H.IsSymm] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    H.Adj y x n :=
  TemporalGraph.adj_symm h

/-- An adjacency of a subgraph `H` is an adjacency of the ambient graph `G`. This and the two
lemmas `Adj.fst_mem`, `Adj.snd_mem` are aesop `forward` rules: from `h : H.Adj u v t` aesop adds
`G.Adj u v t`, `u ∈ H.verts` and `v ∈ H.verts`. As `apply` rules they misfire: the conclusion
`G.Adj u v t` of `adj_sub` matches any adjacency goal and spawns an endless chain of subgraphs. -/
@[grind →, aesop safe forward (rule_sets := [TemporalGraph])]
protected theorem Adj.adj_sub {H : G.Subgraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    G.Adj u v t :=
  H.adj_sub h

/-- The two endpoints of an adjacency in a loopless subgraph are distinct. -/
@[grind →]
protected theorem Adj.ne {H : Subgraph G} [G.IsLoopless] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    x ≠ y :=
  (H.adj_sub h).ne

/-- `Adj.ne` with the endpoints swapped. -/
@[grind →]
protected theorem Adj.ne' {H : Subgraph G} [G.IsLoopless] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    y ≠ x :=
  (H.adj_sub h).ne'

/-- The first endpoint of an adjacency of `H` belongs to `H.verts`. -/
@[grind →, aesop safe forward (rule_sets := [TemporalGraph])]
protected theorem Adj.fst_mem {H : G.Subgraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    u ∈ H.verts :=
  H.edge_vert h

/-- The second endpoint of an adjacency of `H` belongs to `H.verts`. -/
@[grind →, aesop safe forward (rule_sets := [TemporalGraph])]
protected theorem Adj.snd_mem {H : G.Subgraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    y ∈ H.verts :=
  H.edge_vert' h

/-- Coercion from `H : Subgraph G` to a `TemporalGraph H.verts`. -/
@[simps, coe]
protected def coe (H : Subgraph G) : TemporalGraph H.verts where
  Adj x y n := H.Adj x y n

/-- The subtype view of a symmetric subgraph is symmetric. -/
instance coe_isSymm (H : Subgraph G) [H.IsSymm] : H.coe.IsSymm :=
  .of_adj fun _ _ _ h ↦ H.adj_symm h

/-- The subtype view of a subgraph of a loopless graph is loopless. -/
instance coe_isLoopless (H : Subgraph G) [G.IsLoopless] : H.coe.IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩⟩

/-- An adjacency in the subtype view `H.coe` is an adjacency in the ambient graph `G`. -/
theorem coe_adj_sub (H : Subgraph G) (x y : H.verts) (n : ℕ) (h : H.coe.Adj x y n) :
    G.Adj x y n :=
  H.adj_sub h

/-- An adjacency `h : H.Adj u v t` gives the corresponding adjacency in the subtype view
`H.coe`, at `⟨u, _⟩` and `⟨v, _⟩`: `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩ t`. -/
protected theorem Adj.coe {H : G.Subgraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.coe.Adj ⟨x, H.edge_vert h⟩ ⟨y, H.edge_vert' h⟩ n :=
  h

end CoeAdjacency

section Spanning

/-- `H` is a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (H : Subgraph G) : Prop :=
  ∀ x : V, x ∈ H.verts

/-- A subgraph is spanning iff its vertex set is all of `V`. -/
theorem isSpanning_iff {H : Subgraph G} : H.IsSpanning ↔ H.verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

end Spanning

section Props

instance [Finite V] {H : Subgraph G} : Finite H.verts :=
  H.verts.toFinite

/-- A subgraph is symmetric iff its subtype view `H.coe` is. Deliberately not `@[simp]`, unlike
the other `_iff_coe` lemmas: `IsSymm` is a class, carried by instance resolution (see
`coe_isSymm`), and rewriting it in hypothesis position would only get in the way of that. -/
lemma isSymm_iff_coe {H : Subgraph G} : H.IsSymm ↔ H.coe.IsSymm := by
  constructor
  · intro h
    exact IsSymm.of_adj fun n _ _ h' ↦ (h.symm n).symm _ _ h'
  · intro h
    exact IsSymm.of_adj fun n x y h' ↦
      (h.symm n).symm (⟨x, H.edge_vert h'⟩) (⟨y, H.edge_vert' h'⟩) h'

/-- A subgraph is simple iff its subtype view `H.coe` is. -/
lemma isSimple_iff_coe {H : Subgraph G} : H.IsSimple ↔ H.coe.IsSimple := by
  unfold TemporalGraph.IsSimple
  constructor
  · intro h _ _ _ _ h₁ h₂
    exact h h₁ h₂
  · intro h x y _ _ h₁ h₂
    exact @h ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ _ _ h₁ h₂

/-- `H` is a clique on its own vertex set. Shorthand for `H.IsClique H.verts`. Deliberately not
named `IsClique`: that would shadow the inherited `TemporalGraph.IsClique`, so that
`H.IsClique S` stops resolving and both versions print as `H.IsClique`. -/
abbrev IsCliqueSubgraph (H : Subgraph G) : Prop := H.IsClique H.verts

/-- `H` is a clique on its own vertices iff its subtype view `H.coe` is a clique on all of
`H.verts`. -/
lemma isClique_iff_coe {H : Subgraph G} : H.IsCliqueSubgraph ↔ H.coe.IsCliqueGraph := by
  constructor
  · intro h x _ y _ hne
    exact h x.2 y.2 (fun heq ↦ hne (Subtype.ext heq))
  · intro h x hx y hy hne
    exact h (Set.mem_univ (⟨x, hx⟩ : H.verts)) (Set.mem_univ (⟨y, hy⟩ : H.verts))
      (fun heq ↦ hne (congrArg Subtype.val heq))

/-- A subgraph is proper iff its subtype view `H.coe` is. -/
lemma isProper_iff_coe {H : Subgraph G} : H.IsProper ↔ H.coe.IsProper := by
  unfold TemporalGraph.IsProper
  constructor
  · intro h x y z n h₁ h₂
    exact Subtype.ext (h h₁ h₂)
  · intro h x y z n h₁ h₂
    exact congrArg Subtype.val
      (@h ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ ⟨z, H.edge_vert' h₂⟩ n h₁ h₂)

/-- A subgraph is happy iff its subtype view `H.coe` is. -/
lemma isHappy_iff_coe {H : Subgraph G} : H.IsHappy ↔ H.coe.IsHappy := by
  unfold TemporalGraph.IsHappy
  simp only [isSimple_iff_coe, isProper_iff_coe]

/-- `M` is a matching: every vertex of `M.verts` is adjacent in `M` to exactly one
vertex-time pair `(y, n)`. Analogue of Mathlib's `SimpleGraph.Subgraph.IsMatching`. -/
def IsMatching (M : Subgraph G) : Prop :=
  ∀ ⦃v : V⦄, v ∈ M.verts → ∃! q : V × ℕ, M.Adj v q.1 q.2

/-- `M` is a perfect matching: a matching that is also spanning. Analogue of Mathlib's
`SimpleGraph.Subgraph.IsPerfectMatching`. -/
def IsPerfectMatching (M : Subgraph G) := M.IsMatching ∧ M.IsSpanning

/-- `M` is a perfect matching of `H`: a matching whose vertex set is exactly `H.verts`. -/
def IsPerfectMatchingOf (M : Subgraph G) (H : Subgraph G) :=
  M.IsMatching ∧ M.verts = H.verts

end Props

section incidenceSet

/-- A simple subgraph on finitely many vertices has a finite incidence set at every vertex. -/
lemma finite_incidenceSet_of_finite_simple {H : Subgraph G} [h : Finite H.verts]
    (h₁ : H.IsSimple) :
    ∀ x : V, (H.incidenceSet x).Finite := by
  intro x
  apply Set.Finite.of_injOn (f := fun p : V × ℕ ↦ p.1) (t := H.verts)
  · intro ⟨y, n⟩ hadj
    exact H.edge_vert' hadj
  · intro ⟨y, n⟩ hyn ⟨z, m⟩ hzm heq
    simp only at heq
    subst heq
    congr
    exact h₁ hyn hzm
  · exact h

/-- A `Fintype` structure on the incidence set of a simple subgraph on finitely many vertices,
obtained from `finite_incidenceSet_of_finite_simple` (hence noncomputable). Useful for stating
cardinalities of incidence sets (`Fintype.card`), not for computing with them. This is
deliberately not an instance: `h₀` cannot be synthesised, so an instance carrying it could never
fire. -/
@[instance_reducible]
noncomputable def fintypeIncidenceSetOfSimple (H : Subgraph G) [Finite H.verts]
    (h₀ : H.IsSimple) (x : V) : Fintype (H.incidenceSet x) :=
  (finite_incidenceSet_of_finite_simple h₀ x).fintype

/-- A simple subgraph on finitely many vertices has finitely many edges (at most one time per
pair). -/
lemma finite_edgeSet_of_finite_simple {H : Subgraph G} [Finite H.verts] (h₀ : H.IsSimple) :
    H.edgeSet.Finite := by
  have hsub : H.edgeSet ⊆
      (fun p : V × V × ℕ ↦ (s(p.1, p.2.1), p.2.2)) '' ⋃ x ∈ H.verts, {x} ×ˢ H.incidenceSet x := by
    rintro ⟨p, n⟩ ⟨x, y, hp, hadj⟩
    refine ⟨(x, y, n), ?_, by simp [hp]⟩
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    exact ⟨x, H.edge_vert hadj, rfl, hadj⟩
  refine Set.Finite.subset (Set.Finite.image _ ?_) hsub
  exact (Set.toFinite H.verts).biUnion fun x _ ↦
    (Set.finite_singleton x).prod (finite_incidenceSet_of_finite_simple h₀ x)

/-- In a nontrivial clique subgraph, every vertex has a nonempty incidence set. -/
lemma nonempty_incidenceSet_of_nontrivial_clique {H : Subgraph G} [h : Nontrivial H.verts]
    (h₁ : H.IsCliqueSubgraph) :
    ∀ x ∈ H.verts, (H.incidenceSet x).Nonempty := by
  intro x hx
  have ⟨y, z, hne⟩ := h.exists_pair_ne
  by_cases heq : x = y.1
  · subst heq
    have ⟨n, hadj⟩ := h₁ hx z.2 (fun h' ↦ hne (Subtype.ext h'))
    exact ⟨⟨z.1, n⟩, hadj⟩
  · have ⟨n, hadj⟩ := h₁ hx y.2 heq
    exact ⟨⟨y.1, n⟩, hadj⟩

/-- A vertex with a nonempty, finite incidence set has an earliest edge. -/
lemma earliestEdge_exists_of_nonempty_finite_incidenceSet {x : V} {H : Subgraph G}
    (h₀ : (H.incidenceSet x).Nonempty)
    (h₁ : (H.incidenceSet x).Finite) :
    ∃ (y : V) (n : ℕ), H.EarliestEdge x y n := by
  have : Nonempty (H.incidenceSet x) := Set.nonempty_coe_sort.mpr h₀
  have ⟨⟨⟨y, n⟩, hin⟩, hmin⟩ := h₁.exists_min (fun x ↦ x.1.2)
  use y, n
  -- the chosen pair is an adjacency, and minimal (resp. maximal) for the time among all of them
  refine ⟨hin, fun z m hadj ↦ ?_⟩
  simpa using hmin ⟨⟨z, m⟩, hadj⟩

/-- A vertex with a nonempty, finite incidence set has a latest edge. -/
lemma latestEdge_exists_of_nonempty_finite_incidenceSet {x : V} {H : Subgraph G}
    (h₀ : (H.incidenceSet x).Nonempty)
    (h₁ : (H.incidenceSet x).Finite) :
    ∃ (z : V) (m : ℕ), H.LatestEdge x z m := by
  have : Nonempty (H.incidenceSet x) := Set.nonempty_coe_sort.mpr h₀
  have ⟨⟨⟨y, n⟩, hin⟩, hmax⟩ := h₁.exists_max (fun x ↦ x.1.2)
  use y, n
  -- the chosen pair is an adjacency, and minimal (resp. maximal) for the time among all of them
  refine ⟨hin, fun z m hadj ↦ ?_⟩
  simpa using hmax ⟨⟨z, m⟩, hadj⟩

end incidenceSet

section Order

/-- `⊤ : Subgraph G` is `G` itself: all vertices and all arcs. It needs no hypothesis on `G`. -/
instance : Top G.Subgraph where
  top := {
    verts := Set.univ
    Adj := G.Adj
    adj_sub := id
    edge_vert := @fun x _ _ _ ↦ Set.mem_univ x
    edge_vert' := @fun _ y _ _ ↦ Set.mem_univ y
  }

/-- Adjacency in `⊤ : Subgraph G` is adjacency in `G`. -/
@[simp, grind =]
theorem top_adj {x y : V} {n : ℕ} :
    (⊤ : Subgraph G).Adj x y n ↔ G.Adj x y n :=
  Iff.rfl

/-- The vertex set of `⊤ : Subgraph G` is all of `V`. -/
@[grind =]
theorem top_verts : (⊤ : Subgraph G).verts = Set.univ := rfl

/-- The underlying `TemporalGraph` of `⊤ : Subgraph G` is `G` itself. -/
theorem top_toTemporalGraph : (⊤ : Subgraph G).toTemporalGraph = G := rfl

/-- `⊤ : Subgraph G` is spanning. -/
theorem isSpanning_top : (⊤ : Subgraph G).IsSpanning := by
  simp [IsSpanning, top_verts]

/-- `⊤ : Subgraph G` is symmetric whenever `G` is. -/
instance top_isSymm [hs : G.IsSymm] : (⊤ : Subgraph G).IsSymm := hs

/-- `⊥ : Subgraph G` is the empty subgraph: no vertices and no arcs. -/
instance : Bot G.Subgraph where
  bot := {
    verts := ∅
    Adj := ⊥
    adj_sub := False.elim
    edge_vert := False.elim
    edge_vert' := False.elim
  }

/-- `⊥ : Subgraph G` has no vertices. -/
@[simp, grind =]
theorem bot_verts : (⊥ : Subgraph G).verts = ∅ := rfl

/-- `⊥ : Subgraph G` is symmetric, unconditionally: it has no adjacency to be asymmetric about. -/
instance bot_isSymm : (⊥ : Subgraph G).IsSymm := .of_adj fun _ _ _ ↦ id

/-- `H ≤ H'` when `H`'s vertices are among `H'`'s and every adjacency of `H` is one of `H'`.
Written directly into the instance, as `SimpleGraph.Subgraph` does, rather than through a named
relation that would compete with `TemporalGraph.IsSubgraphOf`. -/
instance : LE (Subgraph G) :=
  ⟨fun H H' ↦ H.verts ⊆ H'.verts ∧ ∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n⟩

/-- `H ≤ H'` unfolds to vertex inclusion and pointwise adjacency implication. -/
@[grind =]
lemma le_def {H H' : Subgraph G} :
    H ≤ H' ↔ H.verts ⊆ H'.verts ∧ ∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n :=
  .rfl

instance : BoundedOrder (Subgraph G) where
  top := ⊤
  bot := ⊥
  le_top x := ⟨Set.subset_univ _, fun h ↦ x.adj_sub h⟩
  bot_le _ := ⟨Set.empty_subset _, False.elim⟩

instance : Preorder (Subgraph G) where
  le_refl H := ⟨by simp, by simp⟩
  le_trans A B C h h' := ⟨h.left.trans h'.left, fun hadj ↦ h'.right (h.right hadj)⟩

instance : PartialOrder (Subgraph G) where
  le_antisymm A B h h' := by
    ext _ _ _
    · exact ⟨h.right, h'.right⟩
    · exact ⟨fun hx ↦ h.left hx, fun hx ↦ h'.left hx⟩

/-- `H < H'` explicitly: either `H` has strictly fewer vertices (and no arc outside `H'`), or the
same vertices and strictly fewer arcs. -/
theorem lt_iff {H H' : Subgraph G} :
    H < H' ↔
      (H.verts ⊂ H'.verts ∧ ∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n) ∨
      (H.verts = H'.verts ∧ (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n) ∧
        ∃ (x y : V) (n : ℕ), H'.Adj x y n ∧ ¬H.Adj x y n) := by
  rw [lt_iff_le_not_ge]
  constructor
  · rintro ⟨⟨hverts, hadj⟩, hnot⟩
    by_cases heq : H.verts = H'.verts
    · -- same vertices: `¬ H' ≤ H` then forces an arc of `H'` missing in `H`
      right
      refine ⟨heq, hadj, ?_⟩
      by_contra hmissing
      push Not at hmissing
      exact hnot ⟨heq.symm.subset, fun h ↦ hmissing _ _ _ h⟩
    · -- different vertices: `H.verts ⊆ H'.verts` is then strict
      exact Or.inl ⟨Set.ssubset_iff_subset_ne.2 ⟨hverts, heq⟩, hadj⟩
  · rintro (⟨hss, hadj⟩ | ⟨heq, hadj, x, y, n, hy, hx⟩)
    · exact ⟨⟨hss.subset, hadj⟩, fun h ↦ hss.not_subset h.1⟩
    · -- `H'` has an arc that `H` lacks, so `H' ≤ H` fails
      exact ⟨⟨heq.subset, hadj⟩, fun h ↦ hx (h.2 hy)⟩

/-- The general inclusion `TemporalGraph.IsSubgraphOf` of two subtype views is the order on
subgraphs: `H.coe` is a subgraph of `H'.coe` iff `H ≤ H'`. -/
theorem isSubgraphOf_coe_iff {H H' : Subgraph G} :
    IsSubgraphOf (P := (· ∈ H.verts)) (P' := (· ∈ H'.verts)) H.coe H'.coe ↔ H ≤ H' := by
  constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨fun x hx ↦ h₀ x hx, fun h ↦ h₁ (x := ⟨_, H.edge_vert h⟩) (y := ⟨_, H.edge_vert' h⟩) h⟩
  · rintro ⟨h₀, h₁⟩
    exact ⟨fun x hx ↦ h₀ hx, fun h ↦ h₁ h⟩

/-- The subtype view of a subgraph is a subgraph, in the general sense of
`TemporalGraph.IsSubgraphOf`, of the subtype view of `⊤`, i.e. of the ambient graph `G`. -/
theorem isSubgraphOf_coe_top (H : Subgraph G) :
    IsSubgraphOf (P := (· ∈ H.verts)) (P' := (· ∈ (⊤ : Subgraph G).verts)) H.coe
      (⊤ : Subgraph G).coe :=
  isSubgraphOf_coe_iff.mpr le_top

/-- The union of two subgraphs: the union of their vertex sets and of their arcs. -/
instance : SemilatticeSup (Subgraph G) where
  sup H₁ H₂ :=
    { verts := H₁.verts ∪ H₂.verts
      Adj x y n := H₁.Adj x y n ∨ H₂.Adj x y n
      adj_sub h := h.elim H₁.adj_sub H₂.adj_sub
      edge_vert h := h.elim (fun h ↦ Or.inl (H₁.edge_vert h)) (fun h ↦ Or.inr (H₂.edge_vert h))
      edge_vert' h := h.elim (fun h ↦ Or.inl (H₁.edge_vert' h)) (fun h ↦ Or.inr (H₂.edge_vert' h)) }
  le_sup_left _ _ := ⟨Set.subset_union_left, Or.inl⟩
  le_sup_right _ _ := ⟨Set.subset_union_right, Or.inr⟩
  sup_le _ _ _ h₀ h₁ := ⟨Set.union_subset h₀.1 h₁.1, fun h ↦ h.elim h₀.2 h₁.2⟩

/-- The vertex set of a union of subgraphs is the union of their vertex sets. -/
@[simp, grind =]
theorem sup_verts (H₁ H₂ : Subgraph G) : (H₁ ⊔ H₂).verts = H₁.verts ∪ H₂.verts :=
  rfl

/-- Adjacency in a union of subgraphs holds iff it holds in one of them. -/
@[simp, grind =]
theorem sup_adj {H₁ H₂ : Subgraph G} {x y : V} {n : ℕ} :
    (H₁ ⊔ H₂).Adj x y n ↔ H₁.Adj x y n ∨ H₂.Adj x y n :=
  Iff.rfl

/-- The union of two symmetric subgraphs is symmetric. -/
instance sup_isSymm (H₁ H₂ : Subgraph G) [H₁.IsSymm] [H₂.IsSymm] : (H₁ ⊔ H₂).IsSymm :=
  IsSymm.of_adj fun _ _ _ h ↦ h.imp (·.symm) (·.symm)

/-- `≤` on subgraphs is compatible with the inherited `≤` on `TemporalGraph`, via
`toTemporalGraph`. -/
theorem toTemporalGraph_le {H H' : Subgraph G} (h : H ≤ H') :
    H.toTemporalGraph ≤ H'.toTemporalGraph :=
  h.right

/-- A subgraph's `toTemporalGraph` is a spanning subgraph of the ambient graph `G`. -/
theorem toTemporalGraph_le_self (H : Subgraph G) : H.toTemporalGraph ≤ G :=
  H.adj_sub

end Order

section Induce

/-- `H` is an *induced subgraph* if two vertices of `H` are adjacent in `H` whenever they are
adjacent in `G`. -/
def IsInduced (H : Subgraph G) : Prop :=
  ∀ ⦃x⦄, x ∈ H.verts → ∀ ⦃y⦄, y ∈ H.verts → ∀ ⦃n : ℕ⦄, G.Adj x y n → H.Adj x y n

/-- The top subgraph `⊤` of `G` is induced: it has all the arcs of `G` on its vertices. -/
@[simp] lemma IsInduced.top : (⊤ : G.Subgraph).IsInduced :=
  fun _ _ _ _ _ ↦ id

/-- The subgraph of `H` induced on `s`; it need not be an induced subgraph of `G` (see
`IsInduced`). -/
@[simps]
def induce (H : G.Subgraph) (s : Set V) : G.Subgraph where
  verts := s
  Adj x y n := x ∈ s ∧ y ∈ s ∧ H.Adj x y n
  adj_sub h := H.adj_sub h.2.2
  edge_vert h := h.1
  edge_vert' h := h.2.1

/-- The induced subgraph of a symmetric subgraph is symmetric. -/
instance induce_isSymm (H : G.Subgraph) [H.IsSymm] (s : Set V) :
    (H.induce s).IsSymm :=
  .of_adj fun _ _ _ h ↦ ⟨h.2.1, h.1, TemporalGraph.adj_symm h.2.2⟩

/-- Inducing `⊤` on any vertex set yields an induced subgraph. -/
lemma isInduced_of_top_induce {s : Set V} :
    (induce (⊤ : Subgraph G) s).IsInduced := by
  intro x hx y hy n h
  exact ⟨hx, hy, h⟩

/-- Inducing a finite subgraph on a subset of its vertices stays finite: `(H.induce s).verts` is
`s` itself, so finiteness transfers along `s ⊆ H.verts`. Stated as a lemma rather than an
instance, since `s ⊆ H.verts` is not a class: use with `haveI`. -/
lemma finite_induce_verts (H : Subgraph G) [Finite H.verts] {s : Set V} (h₀ : s ⊆ H.verts) :
    Finite (H.induce s).verts :=
  Finite.Set.subset H.verts h₀

/-- Inducing `H` on a subset of its vertices gives a subgraph of `H`. -/
lemma induce_le_of_subset {H : Subgraph G} {s : Set V} (h₀ : s ⊆ H.verts) : H.induce s ≤ H :=
  ⟨fun _ hv ↦ h₀ hv, fun h ↦ h.2.2⟩

end Induce

section DeleteVerts

/-- Delete the vertices of `s` from `H`: the subgraph induced on `H.verts \ s`. -/
abbrev deleteVerts (H : Subgraph G) (s : Set V) : G.Subgraph :=
  H.induce (H.verts \ s)

/-- The vertex set of `H.deleteVerts s` is `H.verts \ s`. -/
@[grind =]
lemma deleteVerts_verts (H : Subgraph G) (s : Set V) :
    (H.deleteVerts s).verts = H.verts \ s :=
  rfl

/-- Deleting vertices from `H` gives a subgraph below `H`. -/
@[simp]
theorem deleteVerts_le {H : Subgraph G} {s : Set V} : (H.deleteVerts s) ≤ H := by
  constructor <;> simp

/-- Deleting vertices from a symmetric subgraph keeps it symmetric. -/
instance deleteVerts_isSymm (H : Subgraph G) [H.IsSymm] (s : Set V) :
    (H.deleteVerts s).IsSymm :=
  induce_isSymm H _

/-- Deleting vertices from a finite subgraph stays finite: `(H.deleteVerts s).verts` is a subset
of `H.verts`. -/
instance deleteVerts_finite (H : Subgraph G) [Finite H.verts] (s : Set V) :
    Finite (H.deleteVerts s).verts :=
  Finite.Set.subset H.verts deleteVerts_le.1

/-- Deleting vertices before inducing on a set that avoids them changes nothing. -/
lemma deleteVerts_induce_of_subset {H : Subgraph G} {s U : Set V} (h₀ : U ⊆ H.verts \ s) :
    (H.deleteVerts s).induce U = H.induce U := by
  refine le_antisymm (le_def.mpr ⟨subset_rfl, ?_⟩) (le_def.mpr ⟨subset_rfl, ?_⟩)
  · rintro x y n ⟨hx, hy, -, -, hadj⟩
    exact ⟨hx, hy, hadj⟩
  · rintro x y n ⟨hx, hy, hadj⟩
    exact ⟨hx, hy, h₀ hx, h₀ hy, hadj⟩

end DeleteVerts

section AddVerts

/-- Add the vertices of `s` to `H`: the subgraph induced on `H.verts ∪ s`. -/
abbrev addVerts (H : Subgraph G) (s : Set V) : G.Subgraph :=
  H.induce (H.verts ∪ s)

/-- The vertex set of `H.addVerts s` is `H.verts ∪ s`. -/
@[simp, grind =]
lemma addVerts_verts (H : Subgraph G) (s : Set V) : (H.addVerts s).verts = H.verts ∪ s :=
  rfl

/-- Every adjacency of `H` is still one of `H.addVerts s`. -/
lemma addVerts_adj {x y : V} {n : ℕ} {H : Subgraph G} {s : Set V} :
    H.Adj x y n → (H.addVerts s).Adj x y n :=
  fun h ↦ ⟨.inl (H.edge_vert h), .inl (H.edge_vert' h), h⟩

/-- `H` is below `H.addVerts s`. -/
@[simp]
lemma addVerts_le {H : Subgraph G} {s : Set V} : H ≤ (H.addVerts s) := by
  constructor
  · simp
  · intro _ _ _ h
    exact addVerts_adj h

/-- Adding vertices to a symmetric subgraph keeps it symmetric. -/
instance addVerts_isSymm (H : Subgraph G) [H.IsSymm] (s : Set V) :
    (H.addVerts s).IsSymm :=
  induce_isSymm H _

end AddVerts

section AddEdge

variable {x y : V} {n : ℕ}

/-- Add the single, oriented edge `(x, y)` at time `n`. Needs no symmetry whatsoever: use
`addEdge` to add both orientations at once. -/
def addArc (H : Subgraph G) (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    Subgraph G where
  verts := H.verts
  Adj x' y' n' := H.Adj x' y' n' ∨ (x' = x ∧ y' = y ∧ n' = n)
  edge_vert := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩)
    · exact H.edge_vert hadj
    · exact h₁.left
  edge_vert' := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩)
    · exact H.edge_vert' hadj
    · exact h₁.right
  adj_sub := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩)
    · exact H.adj_sub hadj
    · exact h

/-- Add both orientations of the edge between `x` and `y` at time `n`. Unlike `addArc` this
needs `G.IsSymm`, to see the reversed orientation back in `G`. -/
def addEdge (H : Subgraph G) [G.IsSymm] (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    Subgraph G where
  verts := H.verts
  Adj x' y' n' := H.Adj x' y' n' ∨ (x' = x ∧ y' = y ∧ n' = n) ∨ (y' = x ∧ x' = y ∧ n' = n)
  edge_vert := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact H.edge_vert hadj
    · exact h₁.left
    · exact h₁.right
  edge_vert' := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact H.edge_vert' hadj
    · exact h₁.right
    · exact h₁.left
  adj_sub := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact H.adj_sub hadj
    · exact h
    · exact h.symm

variable {H : Subgraph G} {h : G.Adj x y n}
  {h₁ : x ∈ H.verts ∧ y ∈ H.verts}

/-- `H` is below `H.addArc h h₁`, the subgraph obtained by adding the arc `(x, y)` at time `n`. -/
@[simp]
theorem addArc_le : H ≤ addArc H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

/-- The arc `(x, y)` at time `n` just added is indeed an adjacency of `H.addArc h h₁`. -/
@[simp]
theorem addArc_arc : (addArc H h h₁).Adj x y n :=
  Or.inr ⟨rfl, rfl, rfl⟩

/-- Adding an arc does not change the vertex set. -/
@[simp, grind =]
theorem addArc_verts : (addArc H h h₁).verts = H.verts := rfl

/-- `H` is below `H.addEdge h h₁`, the subgraph obtained by adding both orientations of the edge
between `x` and `y` at time `n`. -/
@[simp]
theorem addEdge_le [G.IsSymm] : H ≤ addEdge H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

/-- The orientation `(x, y)` at time `n` of the edge just added is an adjacency of
`H.addEdge h h₁`. -/
@[simp]
theorem addEdge_edge [G.IsSymm] : (addEdge H h h₁).Adj x y n :=
  Or.inr <| Or.inl ⟨rfl, rfl, rfl⟩

/-- Adding an edge does not change the vertex set. -/
@[simp, grind =]
theorem addEdge_verts [G.IsSymm] : (addEdge H h h₁).verts = H.verts := rfl

/-- The oriented `addArc` is the weaker of the two constructions. -/
theorem addArc_le_addEdge [G.IsSymm] : addArc H h h₁ ≤ addEdge H h h₁ :=
  ⟨subset_rfl, fun hadj ↦ hadj.elim Or.inl (fun h' ↦ Or.inr <| Or.inl h')⟩

instance addEdge_isSymm (H : Subgraph G) [G.IsSymm] [H.IsSymm]
    (h : G.Adj x y n) (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    (addEdge H h h₁).IsSymm := by
  refine IsSymm.of_adj ?_
  intro m _ _ hadj
  -- the old arcs are reversed by symmetry of `H`; the two new orientations are swapped
  rcases hadj with hadj | hxy | hyx
  · exact Or.inl (TemporalGraph.adj_symm hadj)
  · exact Or.inr (Or.inr hxy)
  · exact Or.inr (Or.inl hyx)

end AddEdge

section EdgeProps

variable {x y : V} {n : ℕ}

/-- `(x, y, n)` is `⊤ : Subgraph G`'s earliest edge at `x` iff it is `G`'s. -/
lemma top_earliestEdge :
    (⊤ : Subgraph G).EarliestEdge x y n ↔ G.EarliestEdge x y n := by
  simp [TemporalGraph.EarliestEdge, top_adj]

/-- `(x, y, n)` is `⊤ : Subgraph G`'s latest edge at `x` iff it is `G`'s. -/
lemma top_latestEdge :
    (⊤ : Subgraph G).LatestEdge x y n ↔ G.LatestEdge x y n := by
  simp [TemporalGraph.LatestEdge, top_adj]

/-- In a proper subgraph, any adjacency out of `x` to a vertex other than its earliest neighbor
`y` happens strictly after the earliest edge `(x, y, n)`. -/
lemma earliestEdge_lt_of_proper {H : Subgraph G} {z : V} {m : ℕ}
    (h₀ : H.IsProper)
    (h₁ : H.EarliestEdge x y n)
    (h₂ : H.Adj x z m)
    (h₄ : y ≠ z) :
    n < m := by
  refine (h₁.right _ _ h₂).lt_of_ne fun h ↦ h₄ ?_
  -- if the times coincide, properness forces `y = z`
  exact h₀ h₁.left (h ▸ h₂)

/-- `y` is `⊤ : Subgraph G`'s earliest neighbor of `x` iff it is `G`'s. -/
lemma top_earliestNeighbor :
    (⊤ : Subgraph G).EarliestNeighbor x y ↔ G.EarliestNeighbor x y := by
  simp [TemporalGraph.EarliestNeighbor, top_earliestEdge]

/-- `y` is `⊤ : Subgraph G`'s latest neighbor of `x` iff it is `G`'s. -/
lemma top_latestNeighbor :
    (⊤ : Subgraph G).LatestNeighbor x y ↔ G.LatestNeighbor x y := by
  simp [TemporalGraph.LatestNeighbor, top_latestEdge]

/-- If `(x, y, n)` is `G`'s earliest edge at `x` and also an adjacency of `H`, it is the earliest
edge at `x` in the subtype view `H.coe`. -/
lemma coe_earliestEdge_of_graph_earliestEdge {H : Subgraph G}
    (h₀ : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.EarliestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ n := by
  refine ⟨h₁, fun z m hadj ↦ ?_⟩
  -- the extremality of `(x, y, n)` in `G` transfers to the subtype view
  exact h₀.right z m (H.adj_sub hadj)

/-- If `(x, y, n)` is `G`'s latest edge at `x` and also an adjacency of `H`, it is the latest
edge at `x` in the subtype view `H.coe`. -/
lemma coe_latestEdge_of_graph_latestEdge {H : Subgraph G}
    (h₀ : G.LatestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.LatestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ n := by
  refine ⟨h₁, fun z m hadj ↦ ?_⟩
  -- the extremality of `(x, y, n)` in `G` transfers to the subtype view
  exact h₀.right z m (H.adj_sub hadj)

/-- An earliest edge of `H` is an earliest edge of its subtype view `H.coe`. -/
lemma coe_earliestEdge {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.EarliestEdge x y n) :
    H.coe.EarliestEdge x y n :=
  ⟨Adj.coe h₀.left, fun _ _ h ↦ h₀.right _ _ h⟩

/-- An earliest edge of the subtype view `H.coe` is an earliest edge of `H`. -/
lemma earliestEdge_of_coe {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.coe.EarliestEdge x y n) :
    H.EarliestEdge x y n :=
  ⟨h₀.left, fun _ _ h ↦ h₀.right _ _ (Adj.coe h)⟩

/-- If `(x, y, n)` is `G`'s earliest edge at `x` and also an adjacency of `H`, it is `H`'s
earliest edge at `x`. -/
lemma earliestEdge_of_graph_earliestEdge {H : Subgraph G}
    (h₀ : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.EarliestEdge x y n :=
  ⟨h₁, fun _ _ h ↦ h₀.right _ _ (H.adj_sub h)⟩

/-- If `H'`'s earliest edge at `x` is already an adjacency of the smaller `H ≤ H'`, it is `H`'s
earliest edge at `x` too. -/
lemma earliestEdge_of_ge {H H' : Subgraph G} (h₀ : H ≤ H') (h₁ : H'.EarliestEdge x y n)
    (h₂ : H.Adj x y n) :
    H.EarliestEdge x y n :=
  ⟨h₂, fun _ _ h ↦ h₁.right _ _ (h₀.right h)⟩

/-- A latest edge of `H` is a latest edge of its subtype view `H.coe`. -/
lemma coe_latestEdge {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.LatestEdge x y n) :
    H.coe.LatestEdge x y n :=
  ⟨Adj.coe h₀.left, fun _ _ h ↦ h₀.right _ _ h⟩

/-- A latest edge of the subtype view `H.coe` is a latest edge of `H`. -/
lemma latestEdge_of_coe {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.coe.LatestEdge x y n) :
    H.LatestEdge x y n :=
  ⟨h₀.left, fun _ _ h ↦ h₀.right _ _ (Adj.coe h)⟩

/-- If `(x, y, n)` is `G`'s latest edge at `x` and also an adjacency of `H`, it is `H`'s latest
edge at `x`. -/
lemma latestEdge_of_graph_latestEdge {H : Subgraph G}
    (h₀ : G.LatestEdge x y n) (h₁ : H.Adj x y n) :
    H.LatestEdge x y n :=
  ⟨h₁, fun _ _ h ↦ h₀.right _ _ (H.adj_sub h)⟩

/-- If `H'`'s latest edge at `x` is already an adjacency of the smaller `H ≤ H'`, it is `H`'s
latest edge at `x` too. -/
lemma latestEdge_of_ge {H H' : Subgraph G} (h₀ : H ≤ H') (h₁ : H'.LatestEdge x y n)
    (h₂ : H.Adj x y n) :
    H.LatestEdge x y n :=
  ⟨h₂, fun _ _ h ↦ h₁.right _ _ (h₀.right h)⟩

end EdgeProps

section NeighborHoodSet

/-- The neighbor set of `x` in `⊤ : Subgraph G` is `x`'s neighbor set in `G`. -/
theorem top_neighborSet (x : V) :
    (⊤ : G.Subgraph).neighborSet x = G.neighborSet x := rfl

/-- The neighbor set of any vertex is contained in `H.verts`. -/
theorem neighborSet_subset_verts (H : Subgraph G) (x : V) :
    H.neighborSet x ⊆ H.verts := by
  intro _ h
  obtain ⟨_, h⟩ := (H.mem_neighborSet _ _).mp h
  exact H.edge_vert' h

end NeighborHoodSet

section edgeSet

/-- `⊥ : Subgraph G` has no edges. -/
@[simp, grind =]
theorem bot_edgeSet : (⊥ : Subgraph G).edgeSet = ∅ := by
  ext ⟨p, n⟩
  simp only [TemporalGraph.edgeSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, y, -, hadj⟩
  exact hadj

/-- An adjacency of `H` gives the corresponding undirected edge in `H.edgeSet`. This direction
is orientation-free: it needs neither symmetry of `H` nor looplessness of `G` (it is the `Or.inl`
direction of `mem_edgeSet_iff_or`). -/
protected theorem Adj.mem_edgeSet {H : Subgraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    (s(x,y), n) ∈ H.edgeSet :=
  H.mem_edgeSet_iff_or.mpr (Or.inl h)

/-- The edge set is monotone: `H ≤ H'` implies `H.edgeSet ⊆ H'.edgeSet`. -/
@[simp]
lemma edgeSet_mono {H : Subgraph G} {H' : Subgraph G} (h₀ : H ≤ H') :
    H.edgeSet ⊆ H'.edgeSet := by
  intro _ ⟨x, y, hp, h⟩
  exact ⟨x, y, hp, h₀.right h⟩

/-- The edges of a subgraph of `G` are edges of `G` (analogue of Mathlib's
`SimpleGraph.Subgraph.edgeSet_subset`). -/
lemma edgeSet_subset (H : Subgraph G) : H.edgeSet ⊆ G.edgeSet :=
  fun _ ⟨x, y, hp, h⟩ ↦ ⟨x, y, hp, H.adj_sub h⟩

/-- The edges of a union of subgraphs are the union of their edges. -/
@[simp]
theorem sup_edgeSet (H₁ H₂ : Subgraph G) : (H₁ ⊔ H₂).edgeSet = H₁.edgeSet ∪ H₂.edgeSet := by
  ext ⟨p, n⟩
  induction p using Sym2.ind with
  | _ x y =>
    simp only [TemporalGraph.mem_edgeSet_iff_or, sup_adj, Set.mem_union, or_or_or_comm]

/-- For `H'` symmetric, `H ≤ H'` iff `H`'s edges and vertices are among `H'`'s. -/
lemma le_iff_edgeSet_and_verts {H H' : Subgraph G} [H'.IsSymm] :
    H ≤ H' ↔ H.edgeSet ⊆ H'.edgeSet ∧ H.verts ⊆ H'.verts := by
  constructor
  · intro h
    exact ⟨edgeSet_mono h, h.left⟩
  · intro h
    refine ⟨h.right, fun {_ _ _} hadj ↦ ?_⟩
    -- the edge of `H` is an edge of `H'`, and `H'` is symmetric
    rw [← H'.mem_edgeSet]
    exact h.left (Adj.mem_edgeSet hadj)

/-- Adding an edge inserts the corresponding undirected edge into the edge set. -/
@[simp]
lemma addEdge_edgeSet (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts} :
    (H.addEdge h₀ h₁).edgeSet = insert ⟨s(x,y), n⟩ H.edgeSet := by
  ext ⟨p, n'⟩
  induction p using Sym2.ind with
  | _ a b =>
    simp only [Set.mem_insert_iff, Prod.mk.injEq, TemporalGraph.mem_edgeSet_iff_or, addEdge,
      Sym2.eq_iff]
    tauto

instance {H : Subgraph G} [h : Finite H.edgeSet] {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts} :
    Finite (H.addEdge h₀ h₁).edgeSet := by
  rw [H.addEdge_edgeSet]
  infer_instance

/-- Adding vertices does not change the edge set. -/
@[simp]
lemma addVerts_edgeSet {H : Subgraph G} {s : Set V} :
    (H.addVerts s).edgeSet = H.edgeSet := by
  ext ⟨p, n'⟩
  constructor
  · rintro ⟨a, b, hp, _, _, hadj⟩
    exact ⟨a, b, hp, hadj⟩
  · rintro ⟨a, b, hp, hadj⟩
    exact ⟨a, b, hp, Or.inl (H.edge_vert hadj), Or.inl (H.edge_vert' hadj), hadj⟩

instance {H : Subgraph G} {s : Set V} [h₀ : Finite H.edgeSet] :
    Finite (H.addVerts s).edgeSet := by
  rw [addVerts_edgeSet]
  exact h₀

/-- The underlying simple-graph edge set of `H`: pairs `s(x, y)` such that `H` has an adjacency
between `x` and `y` at some time. -/
def footprintEdgeSet (H : Subgraph G) : Set (Sym2 V) :=
  {p | ∃ n x y, p = s(x,y) ∧ H.Adj x y n}

/-- The map from `H`'s time-stamped edge set to its footprint edge set, forgetting the time. -/
def edgeSetToFootprintEdgeSet (H : Subgraph G) : H.edgeSet → H.footprintEdgeSet :=
  fun x ↦ ⟨x.val.fst, by
    obtain ⟨a, b, hp, hadj⟩ := x.2
    exact ⟨x.val.snd, a, b, hp, hadj⟩⟩

/-- `edgeSetToFootprintEdgeSet` is surjective: every footprint edge comes from some time-stamped
edge. -/
lemma edgeSetToFootprintEdgeSet_surjective (H : Subgraph G) :
    Function.Surjective H.edgeSetToFootprintEdgeSet := by
  intro x
  obtain ⟨n, a, b, hp, hadj⟩ := x.prop
  exact ⟨⟨(x.1, n), a, b, hp, hadj⟩, rfl⟩

/-- For a symmetric, simple subgraph, `edgeSetToFootprintEdgeSet` is injective: at most one time
realizes each undirected edge. -/
lemma edgeSetToFootprintEdgeSet_injective (H : Subgraph G) [H.IsSymm]
    (h₀ : H.IsSimple) :
    Function.Injective H.edgeSetToFootprintEdgeSet := by
  intro x y h
  obtain ⟨a, b, hp, hadj⟩ := x.2
  obtain ⟨a', b', hp', hadj'⟩ := y.2
  simp only [edgeSetToFootprintEdgeSet, Subtype.mk.injEq] at h
  ext
  · exact Sym2.ext_iff.mp h _
  · -- the two edges have the same endpoints, in the same or in the reverse order; in both cases
    -- simplicity gives equal times
    rcases Sym2.eq_iff.mp (hp.symm.trans (h.trans hp')) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h₀ hadj hadj'
    · exact h₀ hadj (H.adj_symm hadj')

/-- For a symmetric, simple subgraph, `edgeSetToFootprintEdgeSet` is a bijection between the
edge set and the footprint edge set. -/
lemma edgeSetToFootprintEdgeSet_bijective (H : Subgraph G) [H.IsSymm]
    (h₀ : H.IsSimple) :
    Function.Bijective H.edgeSetToFootprintEdgeSet :=
  ⟨H.edgeSetToFootprintEdgeSet_injective h₀, H.edgeSetToFootprintEdgeSet_surjective⟩

end edgeSet

section Size

/-- The number of vertices of `H`, for `H.verts` a `Fintype`. -/
def order (H : Subgraph G) [Fintype H.verts] := Fintype.card H.verts

/-- `order` is `Set.ncard` of `H.verts`: the instance-free form. -/
theorem order_eq_ncard (H : Subgraph G) [Fintype H.verts] : H.order = H.verts.ncard :=
  Set.fintypeCard_eq_ncard H.verts

/-- Instance-free form of `size_of_simple`: with no finiteness hypothesis needed, `H.edgeSet` and
`H.footprintEdgeSet` have the same `Set.ncard` when `H` is symmetric and simple. -/
lemma ncard_edgeSet_of_simple (H : Subgraph G) [H.IsSymm] (h₀ : H.IsSimple) :
    H.edgeSet.ncard = H.footprintEdgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.ofBijective _ (H.edgeSetToFootprintEdgeSet_bijective h₀))

/-- For a symmetric, simple subgraph with finitely many edges, `H.size` equals the cardinality of
its footprint edge set. -/
theorem size_of_simple (H : Subgraph G) [H.IsSymm] [Fintype H.edgeSet] (h₀ : H.IsSimple) :
    H.size = H.footprintEdgeSet.ncard := by
  rw [size_eq_ncard]
  exact H.ncard_edgeSet_of_simple h₀

/-- Instance-free form of `addEdge_size`: adding an edge not already present increases the edge
set's `Set.ncard` by exactly one. -/
theorem ncard_edgeSet_addEdge (H : Subgraph G) {x y : V} {n : ℕ}
    [H.IsSymm] [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts}
    {h₂ : ¬H.Adj x y n}
    (hfin : H.edgeSet.Finite := by toFinite_tac) :
    (H.addEdge h₀ h₁).edgeSet.ncard = H.edgeSet.ncard + 1 := by
  rw [H.addEdge_edgeSet]
  exact Set.ncard_insert_of_notMem (fun hm ↦ h₂ (H.mem_edgeSet.mp hm)) hfin

/-- Adding an edge not already present increases `H.size` by exactly one. -/
theorem addEdge_size (H : Subgraph G) {x y : V} {n : ℕ}
    [H.IsSymm] [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts}
    {h₂ : ¬H.Adj x y n}
    [Fintype H.edgeSet] [Fintype (H.addEdge h₀ h₁).edgeSet]
    (hfin : H.edgeSet.Finite := by toFinite_tac) :
    (H.addEdge h₀ h₁).size = H.size + 1 := by
  rw [size_eq_ncard, size_eq_ncard]
  exact H.ncard_edgeSet_addEdge (h₂ := h₂) hfin

/-- Instance-free form of `addEdge_size_le`: adding an edge increases the edge set's
`Set.ncard` by at most one. -/
theorem ncard_edgeSet_addEdge_le (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts} :
    (H.addEdge h₀ h₁).edgeSet.ncard ≤ H.edgeSet.ncard + 1 := by
  rw [H.addEdge_edgeSet]
  exact Set.ncard_insert_le _ _

/-- Adding an edge increases `H.size` by at most one. -/
theorem addEdge_size_le (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts}
    [Fintype H.edgeSet] [Fintype (H.addEdge h₀ h₁).edgeSet] :
    (H.addEdge h₀ h₁).size ≤ H.size + 1 := by
  rw [size_eq_ncard, size_eq_ncard]
  exact H.ncard_edgeSet_addEdge_le

/-- Instance-free form of `addVerts_size`: adding vertices does not change the edge set's
`Set.ncard`. -/
theorem ncard_edgeSet_addVerts {H : Subgraph G} {s : Set V} :
    (H.addVerts s).edgeSet.ncard = H.edgeSet.ncard :=
  congrArg Set.ncard addVerts_edgeSet

/-- Adding vertices does not change `H.size`. -/
@[simp]
theorem addVerts_size {H : Subgraph G} {s : Set V}
    [Fintype H.edgeSet] [Fintype (H.addVerts s).edgeSet] :
    (H.addVerts s).size = H.size := by
  rw [size_eq_ncard, size_eq_ncard]
  exact ncard_edgeSet_addVerts

end Size

end Subgraph

section Construction

variable {V : Type u} {G : TemporalGraph V}

/-- View a `TemporalGraph` `H ≤ G` as a (spanning) `Subgraph G`. The `simps` lemma is restricted to
`verts`: `Adj` is the bare projection `H.Adj` of an opaque `H`, which `simps` cannot unfold, so
`toSubgraph_adj` below restates it by hand. -/
@[simps! verts]
def toSubgraph (H : TemporalGraph V) (h : H ≤ G) : G.Subgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  edge_vert' _ := Set.mem_univ _

/-- Adjacency in `toSubgraph H h` is adjacency in `H`. -/
@[simp, grind =]
theorem toSubgraph_adj (H : TemporalGraph V) (h : H ≤ G) {x y : V} {n : ℕ} :
    (toSubgraph H h).Adj x y n ↔ H.Adj x y n :=
  Iff.rfl

/-- `toSubgraph H h` is spanning. -/
theorem toSubgraph_isSpanning (H : TemporalGraph V) (h : H ≤ G) :
    (toSubgraph H h).IsSpanning :=
  Set.mem_univ

/-- `toSubgraph H h` is symmetric whenever `H` is. -/
instance toSubgraph_isSymm (H : TemporalGraph V) [hs : H.IsSymm] (h : H ≤ G) :
    (toSubgraph H h).IsSymm :=
  hs

namespace Subgraph

/-- The subgraph of `G` spanned by a set `s` of edges; the edges of `s` not in `G.edgeSet` are
ignored. Unlike `TemporalGraph.fromEdgeSet` (in `Basic.lean`, a plain symmetrized `TemporalGraph`),
it lives in the `Subgraph` namespace, so it must be called qualified, as
`Subgraph.fromEdgeSet G s`: dot notation `G.fromEdgeSet` resolves to the `Basic.lean` one. -/
@[simps!]
def fromEdgeSet (G : TemporalGraph V) (s : Set ((Sym2 V) × ℕ)) :
    Subgraph G where
  verts := {x | ∃ (p : s), x ∈ p.1.1}
  Adj x y n := ∃ (a : s), x ∈ a.1.1 ∧ y ∈ a.1.1 ∧ n = a.1.2 ∧ G.Adj x y n
  adj_sub := fun ⟨_, _, _, _, h⟩ ↦ h
  edge_vert := fun ⟨a, hx, _⟩ ↦ ⟨a, hx⟩
  edge_vert' := fun ⟨a, _, hy, _⟩ ↦ ⟨a, hy⟩

/-- `Subgraph.fromEdgeSet G s` is symmetric whenever `G` is. -/
instance fromEdgeSet_isSymm (G : TemporalGraph V) [G.IsSymm] (s : Set ((Sym2 V) × ℕ)) :
    (fromEdgeSet G s).IsSymm := by
  refine IsSymm.of_adj ?_
  rintro n x y ⟨a, hx, hy, hn, hG⟩
  exact ⟨a, hy, hx, hn, hG.symm⟩

/-- If `s` is a set of `G`'s edges, the subgraph built from `s` has edge set exactly `s`. -/
@[simp]
theorem fromEdgeSet_eq {G : TemporalGraph V} [G.IsSymm] [G.IsLoopless]
    {s : Set ((Sym2 V) × ℕ)} (h₀ : s ⊆ G.edgeSet) :
    (fromEdgeSet G s).edgeSet = s := by
  ext ⟨p, n⟩
  constructor
  · rintro ⟨x, y, hp, a, hxa, hya, hna, hG⟩
    have heq : a.1.1 = s(x, y) := a.1.1.mem_and_mem_iff hG.ne |>.mp ⟨hxa, hya⟩
    have hpa : (p, n) = a.1 := Prod.ext (hp.trans heq.symm) hna
    rw [hpa]
    exact a.2
  · intro ha
    obtain ⟨x, y⟩ := p
    exact ⟨x, y, rfl, ⟨(s(x, y), n), ha⟩, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _, rfl,
      G.mem_edgeSet.mp (h₀ ha)⟩

/-- A subgraph built from edges of `H` lies in `H`. -/
lemma fromEdgeSet_le {H : Subgraph G} [G.IsLoopless] [H.IsSymm] {E : Set (Sym2 V × ℕ)}
    (h₀ : E ⊆ H.edgeSet) : Subgraph.fromEdgeSet G E ≤ H := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨⟨⟨e, n⟩, he⟩, hv⟩
    induction e using Sym2.ind with
    | _ a b =>
      have hadj := H.mem_edgeSet.mp (h₀ he)
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact H.edge_vert hadj
      · exact H.edge_vert' hadj
  · rintro x y n ⟨⟨⟨e, m⟩, he⟩, hx, hy, rfl, hG⟩
    have heq : e = s(x, y) := e.mem_and_mem_iff hG.ne |>.mp ⟨hx, hy⟩
    have hmem := h₀ he
    rw [heq] at hmem
    exact H.mem_edgeSet.mp hmem

/-- `Subgraph.fromEdgeSet` is monotone in the edge set. -/
lemma fromEdgeSet_mono {E E' : Set (Sym2 V × ℕ)} (h₀ : E ⊆ E') :
    Subgraph.fromEdgeSet G E ≤ Subgraph.fromEdgeSet G E' := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨⟨p, hp⟩, hv⟩
    exact ⟨⟨p, h₀ hp⟩, hv⟩
  · rintro x y n ⟨⟨p, hp⟩, hx, hy, hn, hG⟩
    exact ⟨⟨p, h₀ hp⟩, hx, hy, hn, hG⟩

/-- An edge of `E` that lies in `G` is an adjacency of every subgraph above
`Subgraph.fromEdgeSet G E`. -/
lemma adj_of_fromEdgeSet_le {K : Subgraph G} {E : Set (Sym2 V × ℕ)} {a b : V} {n : ℕ}
    (h₀ : Subgraph.fromEdgeSet G E ≤ K) (h₁ : (s(a, b), n) ∈ E) (h₂ : G.Adj a b n) :
    K.Adj a b n :=
  h₀.right ⟨⟨(s(a, b), n), h₁⟩, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _, rfl, h₂⟩

/-- An edge of `E` that is an arc of `G` is an arc of `Subgraph.fromEdgeSet G E`. -/
lemma adj_fromEdgeSet {E : Set (Sym2 V × ℕ)} {a b : V} {n : ℕ} (h₀ : (s(a, b), n) ∈ E)
    (h₁ : G.Adj a b n) : (Subgraph.fromEdgeSet G E).Adj a b n :=
  adj_of_fromEdgeSet_le le_rfl h₀ h₁

/-- If a relation `R` gives each `a ∈ A` a unique partner `(v, n)` with `v ∈ B` and `R v a n`,
then there is a set `E` of at most `|A|` edges `(s(v, a), n)` that contains every such edge, has an
edge at every `a ∈ A`, and consists only of such edges. -/
lemma exists_matchingEdges {A B : Set V} {R : V → V → ℕ → Prop} (h₀ : A.Finite)
    (h₁ : ∀ a ∈ A, ∃! q : V × ℕ, q.1 ∈ B ∧ R q.1 a q.2) :
    ∃ E : Set (Sym2 V × ℕ), E.ncard ≤ A.ncard ∧
      (∀ a ∈ A, ∀ v n, v ∈ B → R v a n → (s(v, a), n) ∈ E) ∧
      (∀ a ∈ A, ∃ v n, (s(v, a), n) ∈ E) ∧
      ∀ e ∈ E, ∃ v a n, v ∈ B ∧ a ∈ A ∧ R v a n ∧ e = (s(v, a), n) := by
  classical
  -- the chosen partner of `a`, with a dummy value off `A`
  let f : V → V × ℕ := fun a ↦ if ha : a ∈ A then (h₁ a ha).exists.choose else (a, 0)
  have hf : ∀ a ∈ A, (f a).1 ∈ B ∧ R (f a).1 a (f a).2 := fun a ha ↦ by
    simpa only [f, ha, ↓reduceDIte] using (h₁ a ha).exists.choose_spec
  refine ⟨(fun a ↦ (s((f a).1, a), (f a).2)) '' A, Set.ncard_image_le h₀, ?_, ?_, ?_⟩
  · -- uniqueness: any admissible partner is the chosen one
    intro a ha v n hv hR
    have : (v, n) = f a := by
      simpa only [f, ha, ↓reduceDIte] using
        (h₁ a ha).unique ⟨hv, hR⟩ (h₁ a ha).exists.choose_spec
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp this
    exact ⟨a, ha, rfl⟩
  · exact fun a ha ↦ ⟨(f a).1, (f a).2, a, ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨(f a).1, a, (f a).2, (hf a ha).1, ha, (hf a ha).2, rfl⟩

end Subgraph

end Construction

end TemporalGraph
