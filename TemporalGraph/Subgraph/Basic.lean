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

This file defines `TemporalGraph.Subgraph`, its bounded order, and the constructions that
restrict or enlarge the vertex set. Adding edges, edge sets and sizes are in
`Subgraph/Operations.lean` and `Subgraph/EdgeSet.lean`; `Subgraph.lean` imports all three.

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
* The edge-indexed notions `neighborSet`, `incidenceSet`, `edgeSet` and `size` are inherited from
  `TemporalGraph`.
* `Subgraph.induce`, `Subgraph.deleteVerts`, `Subgraph.addVerts` : restricting or enlarging the
  vertex set.

## Main results

* Coe bridge: the instances `Subgraph.coe_isSymm`, `Subgraph.coe_isLoopless` and the lemmas above.
* Order: `BoundedOrder`, `PartialOrder` and `SemilatticeSup` instances on `Subgraph G`, with `⊤`
  the whole of `G`, `⊥` the empty subgraph and `⊔` the union of vertex sets and arcs; `le_def`,
  `lt_iff`, `toTemporalGraph_le`, `toTemporalGraph_le_self`.
* Induce, delete, add: `induce_le_of_subset`, `deleteVerts_le`, `addVerts_le`.
* Earliest and latest edges: `earliestEdge_exists_of_nonempty_finite_incidenceSet` and its
  `latest` counterpart.

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

end Subgraph

end TemporalGraph
