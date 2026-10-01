/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.TemporalWalk

/-!
# Sub-temporal-graphs

A subgraph of a temporal graph is a set of vertices together with a temporal adjacency relation
that refines the ambient graph's and whose edges have both endpoints in that vertex set. Unlike
Mathlib's `SimpleGraph.Subgraph`, symmetry is not a field: a subgraph may be oriented, and the
symmetric world is entered by assuming `[H.IsSymm]`.

This file defines `TemporalGraph.Subgraph`, its bounded order, the constructions that build one
(`induce`, `deleteVerts`, `addVerts`, `addArc`, `addEdge`, `toSubgraph`, `fromEdgeSet`), and
the subgraph counterparts of the vertex- and edge-indexed notions of `TemporalGraph.Basic`.

## Main definitions

* `TemporalGraph.Subgraph G` : the type of subgraphs of `G : TemporalGraph V`.
* `TemporalGraph.Subgraph.coe` : the view of `H : Subgraph G` as a `TemporalGraph H.verts`.
* `TemporalGraph.Subgraph.IsSpanning`, `TemporalGraph.Subgraph.IsInduced` : whether a subgraph
  carries all of `G`'s vertices, resp. all of `G`'s edges between its own vertices.
* `TemporalGraph.Subgraph.IsMatching`, `TemporalGraph.Subgraph.IsPerfectMatching` : the
  predicates quantifying over `H.verts`. `IsClique` needs no `Subgraph` duplicate: it already
  takes a `Set V` argument, so `H.IsClique H.verts` resolves through the inherited
  `TemporalGraph.IsClique`; `TemporalGraph.Subgraph.IsCliqueSubgraph` abbreviates it.
* `TemporalGraph.Subgraph.order` : the one remaining vertex-counting notion that needs `H.verts`.
  `neighborSet`, `incidenceSet` and `size` need no `Subgraph` duplicate any more: they resolve
  through generalized field notation to the `TemporalGraph` ones (see `Basic.lean`).
* `TemporalGraph.Subgraph.induce`, `TemporalGraph.Subgraph.deleteVerts`,
  `TemporalGraph.Subgraph.addVerts`, `TemporalGraph.Subgraph.addArc`,
  `TemporalGraph.Subgraph.addEdge` : the constructions turning a subgraph into another one.
  `addArc` adds a single orientation and needs no symmetry; `addEdge` adds both, and needs
  `[G.IsSymm]`.
* `TemporalGraph.toSubgraph`, `TemporalGraph.Subgraph.fromEdgeSet` : the constructions producing a
  subgraph from a temporal graph below `G`, resp. from a set of edges.

## Main results

* Instances `BoundedOrder (Subgraph G)` and `PartialOrder (Subgraph G)`, with `⊤` the whole of `G`
  and `⊥` the empty subgraph.
* `TemporalGraph.Subgraph.le_iff_edgeSet_and_verts` : a symmetric subgraph is below another
  exactly when its vertices and its edges are.
* `TemporalGraph.Subgraph.earliestEdge_exists_of_nonempty_finite_incidenceSet` and its `latest`
  counterpart : a vertex with a nonempty finite incidence set has an earliest, resp. latest, edge.
* `TemporalGraph.Subgraph.edgeSetToFootprintEdgeSet_bijective` : for a symmetric, simple subgraph,
  edges and footprint edges are in bijection.

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

universe u

namespace TemporalGraph


@[ext]
structure Subgraph {V : Type u} (G : TemporalGraph V) extends TemporalGraph V where
  verts : Set V

  adj_sub : ∀ {x y : V} {n : ℕ}, Adj x y n → G.Adj x y n
  edge_vert : ∀ {x y : V} {n : ℕ}, Adj x y n → x ∈ verts
  edge_vert' : ∀ {x y : V} {n : ℕ}, Adj x y n → y ∈ verts

namespace Subgraph

variable {V : Type u} {G : TemporalGraph V}

section CoeAdjacency

-- `IsSymm` is no longer redefined here: `Subgraph` now `extends TemporalGraph V`, so
-- `H.IsSymm` resolves through generalized field notation to
-- `TemporalGraph.IsSymm H.toTemporalGraph`.

/-- A subgraph of a loopless graph is loopless: an instance, so that `[G.IsLoopless]` alone
suffices at every use site, however deeply the subgraph is built up. -/
instance loopless (H : Subgraph G) [G.IsLoopless] : H.IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩⟩

@[simp, aesop safe (rule_sets := [TemporalGraph])]
protected theorem irrefl {H : Subgraph G} [G.IsLoopless] {x : V} {n : ℕ} :
    ¬H.Adj x x n :=
  TemporalGraph.irrefl

theorem adj_comm (H : Subgraph G) [H.IsSymm] (x y : V) (n : ℕ) :
    H.Adj x y n ↔ H.Adj y x n :=
  TemporalGraph.adj_comm x y n

-- No attribute here: symmetry is handled once, on `TemporalGraph.adj_symm` (see `Basic.lean`),
-- which applies to `H.Adj` since it *is* `H.toTemporalGraph.Adj`.
theorem adj_symm (H : Subgraph G) [H.IsSymm] {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.Adj y x n :=
  TemporalGraph.adj_symm h

-- No aesop/`symm` attribute: as a `safe` apply rule it made aesop loop;
-- see `TemporalGraph.adj_symm`.
protected theorem Adj.symm {H : Subgraph G} [H.IsSymm] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    H.Adj y x n :=
  TemporalGraph.adj_symm h

-- `forward` rules: from `h : H.Adj u v t` aesop adds `G.Adj u v t`, `u ∈ H.verts`, `v ∈ H.verts`.
-- As `apply` rules they misfired: `adj_sub`'s conclusion `G.Adj u v t` matches any adjacency goal
-- and spawns an endless chain of subgraphs, and `fst_mem` got committed to on `v ∈ H.verts`.
@[aesop safe forward (rule_sets := [TemporalGraph])]
protected theorem Adj.adj_sub {H : G.Subgraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    G.Adj u v t :=
  H.adj_sub h

protected theorem Adj.ne {H : Subgraph G} [G.IsLoopless] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    x ≠ y :=
  (H.adj_sub h).ne

protected theorem Adj.ne' {H : Subgraph G} [G.IsLoopless] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    y ≠ x :=
  (H.adj_sub h).ne'

@[aesop safe forward (rule_sets := [TemporalGraph])]
protected theorem Adj.fst_mem {H : G.Subgraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    u ∈ H.verts :=
  H.edge_vert h

@[aesop safe forward (rule_sets := [TemporalGraph])]
protected theorem Adj.snd_mem {H : G.Subgraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    y ∈ H.verts :=
  H.edge_vert' h

/-- Coercion from `H : Subgraph G` to a `TemporalGraph H.verts`. -/
@[simps, coe]
protected def coe (H : Subgraph G) : TemporalGraph H.verts where
  Adj x y n := H.Adj x y n

instance coe_isSymm (H : Subgraph G) [H.IsSymm] : H.coe.IsSymm :=
  .of_adj fun _ _ _ h ↦ H.adj_symm h

instance coe_isLoopless (H : Subgraph G) [G.IsLoopless] : H.coe.IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩⟩

theorem coe_adj_sub (H : Subgraph G) (x y : H.verts) (n : ℕ) (h : H.coe.Adj x y n) :
    G.Adj x y n :=
  H.adj_sub h

-- Given `h : H.Adj u v t`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩ t`.
protected theorem Adj.coe {H : G.Subgraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.coe.Adj ⟨x, H.edge_vert h⟩ ⟨y, H.edge_vert' h⟩ n :=
  h

/-- The subtype view of a subgraph is a subgraph of the ambient graph, in the general sense of
`TemporalGraph.IsSubgraphOf`: its vertices are vertices of `G`, and its adjacencies are `G`'s. -/
theorem coe_sub (H : Subgraph G) :
    IsSubgraphOf H.coe (G : TemporalGraph {x : V // True}) where
  incl _ _ := trivial
  incl' hadj := H.adj_sub hadj

end CoeAdjacency

section Spanning

/-- A Subgraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (H : Subgraph G) : Prop :=
  ∀ x : V, x ∈ H.verts

theorem isSpanning_iff {H : Subgraph G} : H.IsSpanning ↔ H.verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

end Spanning

section Props

-- Deliberately not `@[simp]`, unlike the `isSimple_iff_coe` family below: `IsSymm` is a class,
-- carried by instance resolution (see `coe_isSymm`), and rewriting it in hypothesis position
-- would only get in the way of that.
lemma isSymm_iff_coe {H : Subgraph G} : H.IsSymm ↔ H.coe.IsSymm := by
  constructor
  · intro h
    exact IsSymm.of_adj fun n _ _ h' ↦ (h.symm n).symm _ _ h'
  · intro h
    exact IsSymm.of_adj fun n x y h' ↦
      (h.symm n).symm (⟨x, H.edge_vert h'⟩) (⟨y, H.edge_vert' h'⟩) h'

-- `IsSimple` is no longer redefined here; `H.IsSimple` resolves to `TemporalGraph.IsSimple
-- H.toTemporalGraph`, whose binders are EXPLICIT (unlike the old implicit-binder local
-- definition), so call sites below must supply `x y n m` explicitly.

@[simp]
lemma isSimple_iff_coe {H : Subgraph G} : H.IsSimple ↔ H.coe.IsSimple := by
  unfold TemporalGraph.IsSimple
  constructor
  · intro h _ _ _ _ h'
    exact h _ _ _ _ h'
  · intro h x y _ _ h'
    exact h ⟨x, H.edge_vert h'.1⟩ ⟨y, H.edge_vert' h'.1⟩ _ _ h'

/-- `H` is a clique on its own vertex set. Shorthand for `H.IsClique H.verts`. Deliberately not
named `IsClique`: that would shadow the inherited `TemporalGraph.IsClique`, so that
`H.IsClique S` stops resolving and both versions print as `H.IsClique`. -/
abbrev IsCliqueSubgraph (H : Subgraph G) : Prop := H.IsClique H.verts

@[simp]
lemma isClique_iff_coe {H : Subgraph G} : H.IsCliqueSubgraph ↔ H.coe.IsCliqueGraph := by
  constructor
  · intro h x _ y _ hne
    exact h x.2 y.2 (fun heq ↦ hne (Subtype.ext heq))
  · intro h x hx y hy hne
    exact h (Set.mem_univ (⟨x, hx⟩ : H.verts)) (Set.mem_univ (⟨y, hy⟩ : H.verts))
      (fun heq ↦ hne (congrArg Subtype.val heq))

-- `IsProper` is no longer redefined here; `H.IsProper` resolves to `TemporalGraph.IsProper
-- H.toTemporalGraph`, whose binders are EXPLICIT, so call sites below supply `x y z n` explicitly.

@[simp]
lemma isProper_iff_coe {H : Subgraph G} : H.IsProper ↔ H.coe.IsProper := by
  unfold TemporalGraph.IsProper
  constructor
  · intro h x y z n h'
    have := h x y z n h'
    rw [Subtype.val_inj] at this
    assumption
  · intro h x y z n h'
    have := h ⟨x, H.edge_vert h'.1⟩ ⟨y, H.edge_vert' h'.1⟩ ⟨z, H.edge_vert' h'.2⟩ n h'
    rw [←Subtype.val_inj] at this
    assumption

-- `IsHappy` is no longer redefined here; `H.IsHappy` resolves to `TemporalGraph.IsHappy
-- H.toTemporalGraph`.

@[simp]
lemma isHappy_iff_coe {H : Subgraph G} : H.IsHappy ↔ H.coe.IsHappy := by
  unfold TemporalGraph.IsHappy
  simp only [isSimple_iff_coe, isProper_iff_coe]

instance [Finite V] {H : Subgraph G} : Finite H.verts :=
  H.verts.toFinite


-- From SimpleGraph.Subgraph.IsMatching Revised
def IsMatching (M : Subgraph G) : Prop :=
  ∀ ⦃v : V⦄, v ∈ M.verts → ∃! q : V × ℕ, M.Adj v q.1 q.2

-- From SimpleGraph.Subgraph.IsPerfectMatching
def IsPerfectMatching (M : Subgraph G) := M.IsMatching ∧ M.IsSpanning

def IsPerfectMatchingOf (M : Subgraph G) (H : Subgraph G) :=
  M.IsMatching ∧ M.verts = H.verts

end Props

section incidenceSet

-- `incidenceSet` is no longer redefined here: it never used `verts`, so it now lives on
-- `TemporalGraph` (`Basic.lean`); `H.incidenceSet` resolves to `TemporalGraph.incidenceSet
-- H.toTemporalGraph` through generalized field notation.

lemma finite_incidenceSet_of_finite_simple {H : Subgraph G} [h : Finite H.verts]
    (h₁ : H.IsSimple) :
    ∀ x : V, (H.incidenceSet x).Finite := by
  intro x
  apply Set.Finite.of_injOn (f := fun p : V × ℕ => p.1) (t := H.verts)
  · intro ⟨y, n⟩ hadj ; exact H.edge_vert' hadj
  · intro ⟨y, n⟩ hyn ⟨z, m⟩ hzm heq
    simp only at heq
    subst heq
    congr
    exact h₁ x y n m ⟨hyn, hzm⟩
  · exact h

/-- Noncomputable: obtained from `finite_incidenceSet_of_finite_simple` via `Classical.choice`.
Useful for stating cardinalities of incidence sets (`Fintype.card`), not for computing with them.
This is deliberately not an instance: `h₀` cannot be synthesised, so an instance carrying it could
never fire. -/
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

lemma earliestEdge_exists_of_nonempty_finite_incidenceSet {x : V} {H : Subgraph G}
    (h₀ : (H.incidenceSet x).Nonempty)
    (h₁ : (H.incidenceSet x).Finite) :
    ∃ (y : V) (n : ℕ), H.EarliestEdge x y n := by
  have : Nonempty (H.incidenceSet x) := Set.nonempty_coe_sort.mpr h₀
  have ⟨⟨⟨y, n⟩, hin⟩, hmin⟩ := h₁.exists_min (fun x ↦ x.1.2)
  use y, n
  unfold TemporalGraph.EarliestEdge
  constructor
  · trivial
  · intro z m hadj
    have hin' : ⟨z, m⟩ ∈ H.incidenceSet x := hadj
    have hle := hmin ⟨⟨z, m⟩, hin'⟩
    simp at hle
    trivial

lemma latestEdge_exists_of_nonempty_finite_incidenceSet {x : V} {H : Subgraph G}
    (h₀ : (H.incidenceSet x).Nonempty)
    (h₁ : (H.incidenceSet x).Finite) :
    ∃ (z : V) (m : ℕ), H.LatestEdge x z m := by
  have : Nonempty (H.incidenceSet x) := Set.nonempty_coe_sort.mpr h₀
  have ⟨⟨⟨y, n⟩, hin⟩, hmax⟩ := h₁.exists_max (fun x ↦ x.1.2)
  use y, n
  unfold TemporalGraph.LatestEdge
  constructor
  · trivial
  · intro z m hadj
    have hin' : ⟨z, m⟩ ∈ H.incidenceSet x := hadj
    have hle := hmax ⟨⟨z, m⟩, hin'⟩
    simp at hle
    trivial

end incidenceSet

section Order

/-- The `⊤ : Subgraph G` is `G` itself. Now that symmetry is no longer a field, this
needs no hypothesis on `G` at all. -/
instance : Top G.Subgraph where
  top := {
    verts := Set.univ
    Adj := G.Adj
    adj_sub := id
    edge_vert := @fun x _ _ _ ↦ Set.mem_univ x
    edge_vert' := @fun _ y _ _ ↦ Set.mem_univ y
  }

@[simp]
theorem top_adj {x y : V} {n : ℕ} :
    (⊤ : Subgraph G).Adj x y n ↔ G.Adj x y n :=
  Iff.rfl

theorem top_verts : (⊤ : Subgraph G).verts = Set.univ := rfl

theorem top_toTemporalGraph : (⊤ : Subgraph G).toTemporalGraph = G := rfl

theorem top_isSpanning : (⊤ : Subgraph G).IsSpanning := by
  simp [IsSpanning, top_verts]

instance top_isSymm [hs : G.IsSymm] : (⊤ : Subgraph G).IsSymm := hs

/-- The `⊥ : Subgraph G` is the empty graph where there is no vertices. -/
instance : Bot G.Subgraph where
  bot := {
    verts := ∅
    Adj := ⊥
    adj_sub := False.elim
    edge_vert := False.elim
    edge_vert' := False.elim
  }

instance bot_isSymm : (⊥ : Subgraph G).IsSymm := .of_adj fun _ _ _ ↦ id

/-- `H ≤ H'` when `H`'s vertices are among `H'`'s and every adjacency of `H` is one of `H'`.
Written directly into the instance, as `SimpleGraph.Subgraph` does, rather than through a named
relation that would compete with `TemporalGraph.IsSubgraphOf`. -/
instance : LE (Subgraph G) :=
  ⟨fun H H' => H.verts ⊆ H'.verts ∧ ∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n⟩

instance : BoundedOrder (Subgraph G) where
  top := ⊤
  bot := ⊥
  le_top x := ⟨Set.subset_univ _, by intro _ _ _ h ; rw [top_adj] ; exact x.adj_sub h⟩
  bot_le _ := ⟨Set.empty_subset _, False.elim⟩

instance : LT (Subgraph G) where
  lt H H' :=
    ((H.verts ⊂ H'.verts) ∧ (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n))
    ∨
    ((H.verts = H'.verts) ∧ (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n)
      ∧ (∃ (x y : V) (n : ℕ), H'.Adj x y n ∧ ¬ H.Adj x y n))

instance : Preorder (Subgraph G) where
  le_refl H := ⟨by simp, by simp⟩
  le_trans A B C h h' := ⟨h.left.trans h'.left , by
    intro _ _ _ hadj
    exact h'.right <| h.right hadj
  ⟩
  lt_iff_le_not_ge A B := by
    constructor
    · intro h ; constructor
      · apply h.elim
        · intro h' ; exact ⟨h'.left.subset, h'.right⟩
        · intro h' ; exact ⟨h'.left.subset, h'.right.left⟩
      · apply h.elim
        · intro h h' ; apply h'.left.not_ssubset ; exact h.left
        · intro h h' ; have ⟨x, y, t, hB, hnA⟩ := h.right.right ; apply hnA.elim ; exact h'.right hB
    · intro h ; apply h.left.left.eq_or_ssubset.elim
      · intro h' ; right ; constructor
        · assumption
        · constructor
          · exact h.left.right
          · have h := h.right ; dsimp [LE.le] at h ; push Not at h
            exact h h'.symm.subset
      · intro h' ; left ; constructor
        · assumption
        · exact h.left.right

instance : PartialOrder (Subgraph G) where
  le_antisymm A B h h' := by
    ext _ _ _
    · exact ⟨h.right, h'.right⟩
    · constructor
      · intro h'' ; apply h.left ; assumption
      · intro h'' ; apply h'.left ; assumption

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

@[simp]
theorem sup_verts (H₁ H₂ : Subgraph G) : (H₁ ⊔ H₂).verts = H₁.verts ∪ H₂.verts :=
  rfl

@[simp]
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

/-- A Subgraph is called an *induced Subgraph* if vertices of `H` are adjacent if
they are adjacent in `G`. -/
def IsInduced (H : Subgraph G) : Prop :=
  ∀ ⦃x⦄, x ∈ H.verts → ∀ ⦃y⦄, y ∈ H.verts → ∀ ⦃n : ℕ⦄, G.Adj x y n → H.Adj x y n

@[simp] lemma IsInduced.top : (⊤ : G.Subgraph).IsInduced :=
  fun _ _ _ _ _ ↦ id

/-- Create the induced subgraph on `G` from another subgraph on `G`, it might not be induced to `G`.
-/
@[simps]
def induce (H : G.Subgraph) (s : Set V) : G.Subgraph where
  verts := s
  Adj x y n := x ∈ s ∧ y ∈ s ∧ H.Adj x y n
  adj_sub h := H.adj_sub h.2.2
  edge_vert h := h.1
  edge_vert' h := h.2.1

instance induce_isSymm (H : G.Subgraph) [H.IsSymm] (s : Set V) :
    (H.induce s).IsSymm :=
  .of_adj fun _ _ _ h ↦ ⟨h.2.1, h.1, TemporalGraph.adj_symm h.2.2⟩

lemma isInduced_of_top_induce {s : Set V} :
    (induce (⊤ : Subgraph G) s).IsInduced := by
  intro x hx y hy n h
  refine ⟨hx, hy, h⟩

end Induce

section DeleteVerts

abbrev deleteVerts (H : Subgraph G) (s : Set V) : G.Subgraph :=
  H.induce (H.verts \ s)

lemma deleteVerts_verts (H : Subgraph G) (s : Set V) :
    (H.deleteVerts s).verts = H.verts \ s :=
  rfl

@[simp]
theorem deleteVerts_le {H : Subgraph G} {s : Set V} : (H.deleteVerts s) ≤ H := by
  constructor <;> simp

theorem deleteVerts_le' (H : Subgraph G) (s : Set V) : (H.deleteVerts s) ≤ H := by
  constructor <;> simp

instance deleteVerts_isSymm (H : Subgraph G) [H.IsSymm] (s : Set V) :
    (H.deleteVerts s).IsSymm :=
  induce_isSymm H _


end DeleteVerts

section AddVerts

abbrev addVerts (H : Subgraph G) (s : Set V) : G.Subgraph :=
  H.induce (H.verts ∪ s)

@[simp]
lemma addVerts_verts (H : Subgraph G) (s : Set V) : (H.addVerts s).verts = H.verts ∪ s :=
  rfl

lemma addVerts_Adj {x y : V} {n : ℕ} {H : Subgraph G} {s : Set V} :
    H.Adj x y n → (H.addVerts s).Adj x y n := by
  have hinc : H.verts ⊆ (H.addVerts s).verts := by simp
  intro h
  have hin := hinc <| H.edge_vert h
  have hin' := hinc <| H.edge_vert' h
  exact ⟨hin, hin', h⟩

@[simp]
lemma addVerts_le {H : Subgraph G} {s : Set V} : H ≤ (H.addVerts s) := by
  constructor
  · simp
  · intro _ _ _ h ; exact addVerts_Adj h

lemma addVerts_le' (H : Subgraph G) (s : Set V) : H ≤ (H.addVerts s) := addVerts_le

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
  Adj x' y' n' := H.Adj x' y' n' ∨ (x'=x∧y'=y∧n'=n)

  edge_vert := by
    intro _ _ _ hadj
    apply hadj.elim
    · intro h' ; exact H.edge_vert h'
    · intro h' ; rw [h'.left] ; exact h₁.left

  edge_vert' := by
    intro _ _ _ hadj
    apply hadj.elim
    · intro h' ; exact H.edge_vert' h'
    · intro h' ; rw [h'.right.left] ; exact h₁.right

  adj_sub := by
    intro _ _ _ hadj
    apply hadj.elim
    · intro h' ; exact H.adj_sub h'
    · intro h' ; rwa [h'.left, h'.right.left, h'.right.right]

/-- Add both orientations of the edge between `x` and `y` at time `n`. Unlike `addArc` this
needs `G.IsSymm`, to see the reversed orientation back in `G`. -/
def addEdge (H : Subgraph G) [G.IsSymm] (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    Subgraph G where
  verts := H.verts
  Adj x' y' n' := H.Adj x' y' n' ∨ (x'=x∧y'=y∧n'=n) ∨ (y'=x∧x'=y∧n'=n)

  edge_vert := by
    intro _ _ _ hadj
    apply hadj.elim3
    · intro h ; exact H.edge_vert h
    · intro h'' ; rw [h''.left] ; exact h₁.left
    · intro h'' ; rw [h''.right.left] ; exact h₁.right

  edge_vert' := by
    intro _ _ _ hadj
    apply hadj.elim3
    · intro h ; exact H.edge_vert' h
    · intro h'' ; rw [h''.right.left] ; exact h₁.right
    · intro h'' ; rw [h''.left] ; exact h₁.left

  adj_sub := by
    intro _ _ _ h''
    apply h''.elim3
    · intro h'' ; exact H.adj_sub h''
    · intro h'' ; rwa [h''.left.symm, h''.right.left.symm, h''.right.right.symm] at h
    · intro h'' ; rw [h''.left.symm, h''.right.left.symm, h''.right.right.symm] at h
      exact h.symm

variable {H : Subgraph G} {h : G.Adj x y n}
  {h₁ : x ∈ H.verts ∧ y ∈ H.verts}

@[simp]
theorem addArc_le : H ≤ addArc H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

theorem addArc_le' (H : Subgraph G) (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    H ≤ addArc H h h₁ :=
  addArc_le

@[simp]
theorem addArc_arc : (addArc H h h₁).Adj x y n :=
  Or.inr ⟨rfl, rfl, rfl⟩

@[simp]
theorem addArc_verts : (addArc H h h₁).verts = H.verts := rfl

@[simp]
theorem addEdge_le [G.IsSymm] : H ≤ addEdge H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

theorem addEdge_le' (H : Subgraph G) [G.IsSymm] (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    H ≤ addEdge H h h₁ :=
  addEdge_le

@[simp]
theorem addEdge_edge [G.IsSymm] : (addEdge H h h₁).Adj x y n :=
  Or.inr <| Or.inl ⟨rfl, rfl, rfl⟩

@[simp]
theorem addEdge_verts [G.IsSymm] : (addEdge H h h₁).verts = H.verts := rfl

/-- The oriented `addArc` is the weaker of the two constructions. -/
theorem addArc_le_addEdge [G.IsSymm] : addArc H h h₁ ≤ addEdge H h h₁ :=
  ⟨subset_rfl, fun hadj ↦ hadj.elim Or.inl (fun h' ↦ Or.inr <| Or.inl h')⟩

instance addEdge_isSymm (H : Subgraph G) [G.IsSymm] [H.IsSymm]
    (h : G.Adj x y n) (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    (addEdge H h h₁).IsSymm := by
  refine IsSymm.of_adj ?_
  intro m _ _ hadj
  apply hadj.elim3
  · intro h' ; exact Or.inl <| TemporalGraph.adj_symm h'
  · intro h' ; exact Or.inr <| Or.inr h'
  · intro h' ; exact Or.inr <| Or.inl h'

end AddEdge

section EdgeProps

variable {x y : V} {n : ℕ}

-- `EarliestEdge`/`LatestEdge`/`EarliestNeighbor`/`LatestNeighbor` are no longer redefined here;
-- `H.EarliestEdge` etc. resolve to the parent `TemporalGraph` versions on `H.toTemporalGraph`.

lemma top_earliestEdge :
    (⊤ : Subgraph G).EarliestEdge x y n ↔ G.EarliestEdge x y n := by
  simp [TemporalGraph.EarliestEdge, top_adj]

lemma top_latestEdge :
    (⊤ : Subgraph G).LatestEdge x y n ↔ G.LatestEdge x y n := by
  simp [TemporalGraph.LatestEdge, top_adj]

@[simp]
lemma earliestEdge_lt_of_proper {H : Subgraph G} {z : V} {m : ℕ}
    (h₀ : H.IsProper)
    (h₁ : H.EarliestEdge x y n)
    (h₂ : H.Adj x z m)
    (h₄ : y ≠ z) :
    n < m := by
  have hle := h₁.right _ _ h₂
  apply hle.lt_of_ne
  by_contra h
  rw [←h] at h₂
  absurd (h₀ x y z n ⟨h₁.left, h₂⟩)
  exact h₄

lemma top_earliestNeighbor :
    (⊤ : Subgraph G).EarliestNeighbor x y ↔ G.EarliestNeighbor x y := by
  simp [TemporalGraph.EarliestNeighbor, top_earliestEdge]

lemma top_latestNeighbor :
    (⊤ : Subgraph G).LatestNeighbor x y ↔ G.LatestNeighbor x y := by
  simp [TemporalGraph.LatestNeighbor, top_latestEdge]

lemma coe_earliestEdge_of_graph_earliestEdge {H : Subgraph G}
    (h₀ : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.EarliestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ n := by
  constructor
  · exact h₁
  · rw [TemporalGraph.EarliestEdge] at h₀
    rcases h₀ with ⟨hαβ, hmin⟩
    intro z m hadj
    cases z with
    | mk z hz => exact hmin z m <| H.adj_sub hadj

lemma coe_latestEdge_of_graph_latestEdge {H : Subgraph G}
    (h₀ : G.LatestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.LatestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ n := by
  constructor
  · exact h₁
  · rw [TemporalGraph.LatestEdge] at h₀
    rcases h₀ with ⟨_, hmin⟩
    intro z m hadj
    cases z with
    | mk z hz => exact hmin z m <| H.adj_sub hadj

@[simp]
lemma coe_earliestEdge {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.EarliestEdge x y n) :
    H.coe.EarliestEdge x y n := by
  constructor
  · exact Adj.coe h₀.left
  · intro _ _ h
    exact h₀.right _ _ h

@[simp]
lemma earliestEdge_of_coe {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.coe.EarliestEdge x y n) :
    H.EarliestEdge x y n := by
  constructor
  · exact h₀.left
  · intro _ _ h
    exact h₀.right _ _ (Adj.coe h)

lemma earliestEdge_of_graph_earliestEdge {H : Subgraph G}
    (h₀ : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.EarliestEdge x y n := by
  have h := coe_earliestEdge_of_graph_earliestEdge h₀ h₁
  exact earliestEdge_of_coe h

lemma earliestEdge_of_ge {H H' : Subgraph G} (h₀ : H ≤ H') (h₁ : H'.EarliestEdge x y n)
    (h₂ : H.Adj x y n) :
    H.EarliestEdge x y n := by
  constructor
  · trivial
  · intro _ _ h
    exact h₁.right _ _ <| h₀.right h

@[simp]
lemma coe_latestEdge {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.LatestEdge x y n) :
    H.coe.LatestEdge x y n := by
  constructor
  · exact Adj.coe h₀.left
  · intro _ _ h
    exact h₀.right _ _ h

@[simp]
lemma latestEdge_of_coe {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.coe.LatestEdge x y n) :
    H.LatestEdge x y n := by
  constructor
  · exact h₀.left
  · intro _ _ h
    exact h₀.right _ _ (Adj.coe h)

lemma latestEdge_of_graph_latestEdge {H : Subgraph G}
    (h₀ : G.LatestEdge x y n) (h₁ : H.Adj x y n) :
    H.LatestEdge x y n := by
  have h := coe_latestEdge_of_graph_latestEdge h₀ h₁
  exact latestEdge_of_coe h

lemma latestEdge_of_ge {H H' : Subgraph G} (h₀ : H ≤ H') (h₁ : H'.LatestEdge x y n)
    (h₂ : H.Adj x y n) :
    H.LatestEdge x y n := by
  constructor
  · trivial
  · intro _ _ h
    exact h₁.right _ _ <| h₀.right h

end EdgeProps

section NeighborHoodSet

-- `neighborSet` is no longer redefined here; `H.neighborSet` resolves to `TemporalGraph.neighborSet
-- H.toTemporalGraph`, whose binder is `x : V` (not `H.verts`).

theorem neighborhoodSet_top (x : V) :
    (⊤ : G.Subgraph).neighborSet x = G.neighborSet x := rfl

theorem neighborSet_subset_verts (H : Subgraph G) (x : V) :
    H.neighborSet x ⊆ H.verts := by
  intro _ h
  rw [H.mem_neighborSet] at h
  let ⟨_, h⟩ := h
  exact H.edge_vert' h

end NeighborHoodSet

section edgeSet

-- `edgeSet` is no longer redefined here: `Subgraph` now `extends TemporalGraph V`, so
-- `H.edgeSet` resolves through generalized field notation to `TemporalGraph.edgeSet
-- H.toTemporalGraph` — the fixed, hypothesis-free definition from `Basic.lean`.

-- The `Adj → edgeSet` direction is orientation-free: it needs neither symmetry of `H` nor
-- looplessness of `G` (it is just the `Or.inl` direction of `mem_edgeSet_iff_or`).
protected theorem Adj.mem_edgeSet {H : Subgraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    (s(x,y), n) ∈ H.edgeSet :=
  H.mem_edgeSet_iff_or.mpr (Or.inl h)

@[simp]
lemma edgeSet_le {H : Subgraph G} {H' : Subgraph G} (h₀ : H ≤ H') :
    H.edgeSet ⊆ H'.edgeSet := by
  intro _ ⟨x, y, hp, h⟩
  exact ⟨x, y, hp, h₀.right h⟩

lemma le_iff_edgeSet_and_verts {H H' : Subgraph G} [H'.IsSymm] :
    H ≤ H' ↔ H.edgeSet ⊆ H'.edgeSet ∧ H.verts ⊆ H'.verts := by
  constructor
  · intro h
    constructor
    · apply edgeSet_le h
    · exact h.left
  · intro h
    constructor
    · exact h.right
    · intro _ _ _ hadj
      rw [←H'.mem_edgeSet]
      exact Set.mem_of_subset_of_mem h.left (Adj.mem_edgeSet hadj)

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

lemma addEdge_edgeSet' (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    (h₀ : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    (H.addEdge h₀ h₁).edgeSet = insert ⟨s(x,y), n⟩ H.edgeSet :=
  H.addEdge_edgeSet

instance {H : Subgraph G} [h : Finite H.edgeSet] {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts} :
    Finite (H.addEdge h₀ h₁).edgeSet := by
  conv =>
    rhs ; rw [H.addEdge_edgeSet, ←Set.union_singleton]
  apply Set.Finite.union
  · exact h
  · simp only [Set.finite_singleton]


@[simp]
lemma addVerts_edgeSet {H : Subgraph G} {s : Set V} :
    (H.addVerts s).edgeSet = H.edgeSet := by
  ext ⟨p, n'⟩
  constructor
  · rintro ⟨a, b, hp, _, _, hadj⟩
    exact ⟨a, b, hp, hadj⟩
  · rintro ⟨a, b, hp, hadj⟩
    exact ⟨a, b, hp, Or.inl (H.edge_vert hadj), Or.inl (H.edge_vert' hadj), hadj⟩

lemma addVerts_edgeSet' {H : Subgraph G} (s : Set V) :
    (H.addVerts s).edgeSet = H.edgeSet := addVerts_edgeSet

instance {H : Subgraph G} {s : Set V} [h₀ : Finite H.edgeSet] [Finite s] :
    Finite (H.addVerts s).edgeSet := by
  simp only [addVerts_edgeSet, h₀]

-- `edgeSet_toTemporalGraph` is gone: `H.edgeSet` now resolves through generalized field
-- notation to `H.toTemporalGraph.edgeSet` directly, making the old statement a tautology.

def footprintEdgeSet (H : Subgraph G) : Set (Sym2 V) :=
  {p | ∃ n x y, p = s(x,y) ∧ H.Adj x y n}

def edgeSetToFootprintEdgeSet (H : Subgraph G) : H.edgeSet → H.footprintEdgeSet :=
  fun x ↦ ⟨x.val.fst, by
    obtain ⟨a, b, hp, hadj⟩ := x.2
    exact ⟨x.val.snd, a, b, hp, hadj⟩⟩

lemma edgeSetToFootprintEdgeSet_surjective (H : Subgraph G) :
    Function.Surjective H.edgeSetToFootprintEdgeSet := by
  intro x
  obtain ⟨n, a, b, hp, hadj⟩ := x.prop
  exact ⟨⟨(x.1, n), a, b, hp, hadj⟩, rfl⟩

lemma edgeSetToFootprintEdgeSet_injective (H : Subgraph G) [H.IsSymm]
    (h₀ : H.IsSimple) :
    Function.Injective H.edgeSetToFootprintEdgeSet := by
  intro x y h
  obtain ⟨a, b, hp, hadj⟩ := x.2
  obtain ⟨a', b', hp', hadj'⟩ := y.2
  simp only [edgeSetToFootprintEdgeSet, Subtype.mk.injEq] at h
  ext
  · apply Sym2.ext_iff.mp h
  · rcases Sym2.eq_iff.mp (hp.symm.trans (h.trans hp')) with heq | heq
    · rw [heq.1.symm, heq.2.symm] at hadj'
      exact h₀ a b x.1.2 y.1.2 ⟨hadj, hadj'⟩
    · rw [heq.1.symm, heq.2.symm] at hadj'
      exact h₀ a b x.1.2 y.1.2 ⟨hadj, H.adj_symm hadj'⟩

lemma edgeSetToFootprintEdgeSet_bijective (H : Subgraph G) [H.IsSymm]
    (h₀ : H.IsSimple) :
    Function.Bijective H.edgeSetToFootprintEdgeSet :=
  ⟨H.edgeSetToFootprintEdgeSet_injective h₀, H.edgeSetToFootprintEdgeSet_surjective⟩

end edgeSet

section Size

-- `size` is no longer redefined here; `H.size` resolves to `TemporalGraph.size H.toTemporalGraph`
-- (the tautological `size_of_toTemporalGraph` bridge is gone along with it).

def order (H : Subgraph G) [Fintype H.verts] := Fintype.card H.verts

/-- Instance-free form of `size_of_simple`: with no finiteness hypothesis needed, `H.edgeSet` and
`H.footprintEdgeSet` have the same `Set.ncard` when `H` is symmetric and simple. -/
lemma ncard_edgeSet_of_simple (H : Subgraph G) [H.IsSymm] (h₀ : H.IsSimple) :
    H.edgeSet.ncard = H.footprintEdgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.ofBijective _ (H.edgeSetToFootprintEdgeSet_bijective h₀))

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

@[simp]
theorem addEdge_size_le (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts}
    [Fintype H.edgeSet] [Fintype (H.addEdge h₀ h₁).edgeSet] :
    (H.addEdge h₀ h₁).size ≤ H.size + 1 := by
  rw [size_eq_ncard, size_eq_ncard]
  exact H.ncard_edgeSet_addEdge_le

theorem addEdge_size_le' (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    (h₀ : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts)
    [Fintype H.edgeSet] [Fintype (H.addEdge h₀ h₁).edgeSet] :
    (H.addEdge h₀ h₁).size ≤ H.size + 1 :=
  H.addEdge_size_le

/-- Instance-free form of `addVerts_size`: adding vertices does not change the edge set's
`Set.ncard`. -/
theorem ncard_edgeSet_addVerts {H : Subgraph G} {s : Set V} :
    (H.addVerts s).edgeSet.ncard = H.edgeSet.ncard :=
  congrArg Set.ncard addVerts_edgeSet

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

-- `@[simps!]` alone chokes on the `Adj` field here: it is given as the bare projection `H.Adj`
-- of an opaque parameter `H`, so simps cannot unfold it any further to a constructor application.
-- Restricting the auto-generated lemmas to `verts` and restating `Adj` by hand avoids the issue.
@[simps! verts]
def toSubgraph (H : TemporalGraph V) (h : H ≤ G) : G.Subgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  edge_vert' _ := Set.mem_univ _

@[simp]
theorem toSubgraph_Adj (H : TemporalGraph V) (h : H ≤ G) {x y : V} {n : ℕ} :
    (toSubgraph H h).Adj x y n ↔ H.Adj x y n :=
  Iff.rfl

theorem toSubgraph_isSpanning (H : TemporalGraph V) (h : H ≤ G) :
    (toSubgraph H h).IsSpanning :=
  Set.mem_univ

instance toSubgraph_isSymm (H : TemporalGraph V) [hs : H.IsSymm] (h : H ≤ G) :
    (toSubgraph H h).IsSymm :=
  hs

-- `fromEdgeSet` lives in the `Subgraph` namespace (unlike `TemporalGraph.fromEdgeSet` in
-- `Basic.lean`, which builds a plain, symmetrized `TemporalGraph`): dot notation `G.fromEdgeSet`
-- always resolves to the `Basic.lean` one, so this constructor must be called qualified, as
-- `Subgraph.fromEdgeSet G s` — matching Mathlib's `SimpleGraph.fromEdgeSet` precedent for
-- the graph-level name.
namespace Subgraph

/-- Create a `Subgraph G` from a set of edges, the edges not in `G.edgeSet` are ignored. -/
@[simps!]
def fromEdgeSet (G : TemporalGraph V) (s : Set ((Sym2 V) × ℕ)) :
    Subgraph G where
  verts := {x | ∃ (p : s) , x ∈ p.1.1 }
  Adj x y n := ∃ (a : s), x ∈ a.1.1 ∧ y ∈ a.1.1 ∧ n = a.1.2 ∧ G.Adj x y n

  adj_sub h := by
    have ⟨_, h⟩ := h
    exact h.2.2.2

  edge_vert h := by
    obtain ⟨a, h⟩ := h
    use a
    exact h.1

  edge_vert' h := by
    obtain ⟨a, h⟩ := h
    use a
    exact h.2.1

instance fromEdgeSet_isSymm (G : TemporalGraph V) [G.IsSymm] (s : Set ((Sym2 V) × ℕ)) :
    (fromEdgeSet G s).IsSymm := by
  refine IsSymm.of_adj ?_
  intro _ _ _ h
  simp only [fromEdgeSet, Subtype.exists, exists_and_left, exists_prop, Prod.exists, ↓existsAndEq,
    true_and] at ⊢ h
  obtain ⟨a, h⟩ := h
  use a
  simp only [h, h.2.2.2.symm, and_self]

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
    exact ⟨x, y, rfl, ⟨(s(x,y), n), ha⟩, Sym2.mem_iff.mpr (Or.inl rfl),
      Sym2.mem_iff.mpr (Or.inr rfl), rfl, G.mem_edgeSet.mp (h₀ ha)⟩

end Subgraph

end Construction

end TemporalGraph
