/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Basic
public import TemporalGraph.Subgraph
public import TemporalGraph.Bipartite
public import TemporalGraph.Connectivity.Subgraph

/-!
# Dismountability

This module formalizes the *dismountability* argument as revisited by Carnevale, Casteigts &
Corsini (SAND 2025, §§2–3), originally due to Casteigts, Peters & Schoeters (CPS, ICALP 2019 /
JCSS), which underlies the `O(n log n)` spanner bound for temporal cliques: a clique
with no dismountable vertex is small enough (via `vzero`) and structured enough (via the
earliest/latest neighbor bijections) to sparsify inductively. See `Dismountability/Operations.lean`
for the operations (`dismount`, `mount`, `twoHopMount`) that carry out the induction.

A subgraph `H` partitions its vertices into `vminus` (vertices that are someone's earliest
neighbor), `vplus` (vertices that are someone's latest neighbor) and `vzero` (neither). `H` is
`Dismountable` when it is a clique with a vertex that is both an earliest and a latest neighbor;
`TwoHopDismountable` weakens this to allow reaching such a vertex within two hops. When `H` is not
two-hop-dismountable, the earliest/latest neighbor relations become bijections between `vminus`
and `vplus` (`earliestNeighborFn`, `latestNeighborFn`), which forces `vzero` to be empty.

## Main definitions

* `TemporalGraph.Subgraph.Dismountable` : SAND 2025, §2, 1-hop dismountability (the hypothesis of
  Theorem 2.1).
* `TemporalGraph.Subgraph.vminus`, `vplus`, `vzero` : SAND 2025, §3.1, `V⁻`/`V⁺`/`V⁰`, the
  partition of `H.verts` defined just before Lemma 3.1.
* `TemporalGraph.Subgraph.TwoHopDismountable` : SAND 2025, §2.1, `{1,2}`-hop dismountability
  (`k`-hop with `k ≤ 2`).
* `TemporalGraph.Subgraph.earliestNeighborFn`, `latestNeighborFn` : the bijections between
  `vminus` and `vplus` obtained when `H` is not two-hop-dismountable (as `V → V` functions, with
  `Set.MapsTo`/`Set.InjOn`/`Set.BijOn` lemmas, suffixed `_mapsTo`/`_injOn`/`_bijOn`).

## Main results

* `TemporalGraph.Subgraph.partition_of_not_dismountable` : SAND 2025, Lemma 3.1, `vminus`, `vplus`,
  `vzero` partition `H.verts`.
* `TemporalGraph.Subgraph.vplus_ne_neighbor_of_not_twoHopDismountable`,
  `vminus_ne_neighbor_of_not_twoHopDismountable` : SAND 2025, Lemma 3.2, distinct vertices of
  `vplus` (resp. `vminus`) have distinct earliest (resp. latest) neighbors.
* `TemporalGraph.Subgraph.exists_edgeSet_of_earliest`, `exists_edgeSet_of_latest` : each side
  of `{1,2}`-hop dismountability, as a set of 1 or 2 edges of `H` through which `x` reaches (resp.
  is reached by) everything a vertex `y ≠ x` does.
* `ncard_pair_le`, `ncard_le_four` (section `CardHelpers`) : `Set.ncard` bounds on a set given by
  2, resp. 4, elements, shared by the edge-count bounds of `mount`, `twoHopMount`,
  `oneSidedMount` and the sides above.
* `TemporalGraph.Subgraph.existsUnique_vplus_earliestEdge`, `existsUnique_vminus_latestEdge` :
  SAND 2025, Corollary 3.3 (1)–(2), perfect matchings between `vminus` and `vplus` given by the
  earliest (resp. latest) edges.
* `TemporalGraph.Subgraph.earliestNeighborFn_bijOn`, `latestNeighborFn_bijOn` : `Set.BijOn`
  bijections between the sets `vminus` and `vplus` (SAND 2025, Corollary 3.3, via Lemma 3.2).
* `TemporalGraph.Subgraph.vminus_card_eq_vplus_card` : SAND 2025, Corollary 3.3 (3),
  `vminus.ncard = vplus.ncard`.
* `TemporalGraph.Subgraph.vzero_empty_of_not_twoHopDismountable` : SAND 2025, Lemma 3.4,
  `vzero = ∅`.
* `TemporalGraph.Subgraph.earliestEdge_reciprocity`, `latestEdge_reciprocity` : SAND 2025,
  Lemma 3.5 (Reciprocity), first and second statements.
* `TemporalGraph.Subgraph.biclique_of_not_twoHopDismountable` : SAND 2025, Corollary 4.1, the
  bipartite subgraph between `vminus` and `vplus` is a bi-clique when `H` is not
  two-hop-dismountable.
* `TemporalGraph.Subgraph.between_TC_of_not_twoHopDismountable` : SAND 2025, remark after
  Corollary 4.1, this bi-clique is temporally connected.
* `TemporalGraph.reachable_of_earliestEdge_matching`, `reachable_of_latestEdge_matching`
  (section `MatchingConnectivity`) : if `s` reaches `t` and every vertex of `t` (resp. `s`) is the
  endpoint of an earliest (resp. latest) edge of a vertex of `s` (resp. `t`), then `t` (resp. `s`)
  is temporally connected.
* `TemporalGraph.temporallyConnected_of_reachable_of_matchings` (section `MatchingConnectivity`) :
  if `t` is reached from `s` and matched to it on both the earliest-edge and latest-edge side,
  `s ∪ t` is temporally connected (SAND 2025, §4.1, after Corollary 4.1).

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025,
  LIPIcs 330, 6:1–6:18, doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321.
* Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse Spanners*, ICALP 2019 / JCSS
  (original source of the argument).
-/

@[expose] public section

universe u
variable {V : Type u}

namespace TemporalGraph

namespace Subgraph

variable {G : TemporalGraph V}

section CardHelpers

/-- An unordered pair has `Set.ncard` at most 2. Shared by the `mount`/`twoHopMount`/
`oneSidedMount` edge-count bounds below. -/
lemma ncard_pair_le {α : Type*} (a b : α) : ({a, b} : Set α).ncard ≤ 2 := by
  have h1 := Set.ncard_insert_le a ({b} : Set α)
  have h2 := Set.ncard_singleton b
  omega

/-- A set given by (up to) four elements has `Set.ncard` at most 4. Shared by the `twoHopMount`
edge-count bound below. -/
lemma ncard_le_four {α : Type*} (a b c d : α) : ({a, b, c, d} : Set α).ncard ≤ 4 := by
  have h1 := Set.ncard_insert_le a ({b, c, d} : Set α)
  have h2 := Set.ncard_insert_le b ({c, d} : Set α)
  have h3 := Set.ncard_insert_le c ({d} : Set α)
  have h4 := Set.ncard_singleton d
  omega

end CardHelpers

section Partition

/-- SAND 2025, §2: 1-hop dismountability (hypothesis of Theorem 2.1). A clique subgraph `H` is
dismountable when some vertex `x` is both the earliest neighbor of some `y` and the latest
neighbor of some `z`. -/
def Dismountable (H : Subgraph G) :=
  H.IsCliqueSubgraph ∧ ∃ (x y z : V), H.EarliestNeighbor y x ∧ H.LatestNeighbor z x

/-- SAND 2025, §3.1: `V⁻`, defined before Lemma 3.1. The set of vertices that are someone's
earliest neighbor. -/
def vminus (H : Subgraph G) : Set V := {x : V | ∃ y : V, H.EarliestNeighbor y x}

/-- `H.vminus` is contained in `H.verts`. -/
@[simp]
lemma vminus_sub_verts {H : Subgraph G} : H.vminus ⊆ H.verts := by
  intro _ ⟨_, ⟨_, h⟩⟩
  exact H.edge_vert' h.left

instance {H : Subgraph G} [h : Finite H.verts] : Finite H.vminus :=
  Set.Finite.subset (H.verts.finite_coe_iff.mp h) vminus_sub_verts

/-- Noncomputable: obtained from the `Finite` instance above via `Classical.choice`. Useful for
stating cardinalities of `vminus` (`Fintype.card`), not for computing with them. -/
noncomputable instance {H : Subgraph G} [Finite H.verts] : Fintype H.vminus :=
  Fintype.ofFinite _

/-- SAND 2025, §3.1: `V⁺`, defined before Lemma 3.1. The set of vertices that are someone's
latest neighbor. -/
def vplus (H : Subgraph G) : Set V := {x : V | ∃ y : V, H.LatestNeighbor y x}

/-- `H.vplus` is contained in `H.verts`. -/
@[simp]
lemma vplus_sub_verts {H : Subgraph G} : H.vplus ⊆ H.verts := by
  intro _ ⟨_, ⟨_, h⟩⟩
  exact H.edge_vert' h.left

instance {H : Subgraph G} [h : Finite H.verts] : Finite H.vplus :=
  Set.Finite.subset (H.verts.finite_coe_iff.mp h) vplus_sub_verts

/-- Noncomputable: obtained from the `Finite` instance above via `Classical.choice`. Useful for
stating cardinalities of `vplus` (`Fintype.card`), not for computing with them. -/
noncomputable instance {H : Subgraph G} [Finite H.verts] : Fintype H.vplus :=
  Fintype.ofFinite _

/-- SAND 2025, §3.1: `V⁰`, defined before Lemma 3.1. The vertices of `H` that are neither in
`vminus` nor `vplus`. -/
def vzero (H : Subgraph G) : Set V := H.verts \ (H.vminus ∪ H.vplus)

/-- `H.vzero` is contained in `H.verts`. -/
@[simp]
lemma vzero_sub_verts {H : Subgraph G} : H.vzero ⊆ H.verts := by
  intro _ ⟨h, _⟩
  exact h

instance {H : Subgraph G} [h : Finite H.verts] : Finite H.vzero :=
  Set.Finite.subset (H.verts.finite_coe_iff.mp h) vzero_sub_verts

/-- Noncomputable: obtained from the `Finite` instance above via `Classical.choice`. Useful for
stating cardinalities of `vzero` (`Fintype.card`), not for computing with them. -/
noncomputable instance {H : Subgraph G} [Finite H.verts] : Fintype H.vzero :=
  Fintype.ofFinite _

/-- A vertex of `H.vzero` lies in neither `H.vminus` nor `H.vplus`. -/
lemma vzero_mem {H : Subgraph G} : ∀ x : V, x ∈ H.vzero → x ∉ H.vminus ∧ x ∉ H.vplus := by
  intro _ hx
  simp [vzero] at hx
  simp [hx]

/-- `vminus`, `vplus` and `vzero` cover `H.verts`. -/
lemma vunion_eq_univ {H : Subgraph G} : H.vminus ∪ H.vplus ∪ H.vzero = H.verts := by
  simp [vzero]

/-- `H.vplus` and `H.vminus` intersect iff `H` is a dismountable clique. -/
lemma nonempty_vplus_inter_vminus_iff_dismountable (H : Subgraph G) :
    H.IsCliqueSubgraph ∧ (H.vplus ∩ H.vminus).Nonempty ↔ H.Dismountable := by
  rw [Dismountable, Set.nonempty_def, vminus, vplus]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, exists_and_left, exists_and_right, And.comm]

/-- SAND 2025, Lemma 3.1: for a clique that is not dismountable, `vminus`, `vplus` and `vzero`
partition `H.verts` into a disjoint cover. -/
lemma partition_of_not_dismountable {H : Subgraph G} (h₀ : H.IsCliqueSubgraph)
    (h₁ : ¬H.Dismountable) :
    ∀ x ∈ H.verts, ∃! s ∈ ({H.vminus, H.vplus, H.vzero} : Set (Set V)), x ∈ s := by
  intro x hx
  -- a vertex in both `V⁻` and `V⁺` would make `H` dismountable
  have hd : x ∈ H.vminus → x ∉ H.vplus := fun hm hp ↦
    h₁ ((nonempty_vplus_inter_vminus_iff_dismountable H).mp ⟨h₀, x, hp, hm⟩)
  by_cases hm : x ∈ H.vminus
  · refine ⟨H.vminus, ⟨by simp, hm⟩, ?_⟩
    rintro s ⟨(rfl | rfl | rfl), hs⟩
    exacts [rfl, absurd hs (hd hm), absurd hm (vzero_mem x hs).1]
  by_cases hp : x ∈ H.vplus
  · refine ⟨H.vplus, ⟨by simp, hp⟩, ?_⟩
    rintro s ⟨(rfl | rfl | rfl), hs⟩
    exacts [absurd hs hm, rfl, absurd hp (vzero_mem x hs).2]
  · refine ⟨H.vzero, ⟨by simp, hx, by simp [hm, hp]⟩, ?_⟩
    rintro s ⟨(rfl | rfl | rfl), hs⟩
    exacts [absurd hs hm, absurd hs hp, rfl]

end Partition

section TwoHop

/-- SAND 2025, §2.1: `{1,2}`-hop dismountability (`k`-hop, `k ≤ 2`). A clique subgraph `H` is
two-hop dismountable when some vertex `x` is reached within at most two hops both from an
earliest edge and from a latest edge. -/
def TwoHopDismountable (H : Subgraph G) :=
  H.IsCliqueSubgraph
  ∧
  (∃ x : V,
    ((∃ y : V, H.EarliestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.EarliestEdge y z n ∧ H.Adj z x m ∧ m ≤ n))
    ∧
    ((∃ y : V, H.LatestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.LatestEdge y z n ∧ H.Adj z x m ∧ n ≤ m)))

/-- A dismountable clique is `{1,2}`-hop dismountable. -/
@[simp]
lemma twoHopDismountable_of_dismountable {H : Subgraph G} (h : H.Dismountable) :
    H.TwoHopDismountable := by
  constructor
  · exact h.left
  · rcases h.right with ⟨u, α, β, hen, hln⟩
    use u
    constructor <;> apply Or.inl
    · exists α
    · exists β

/-- A subgraph that is not `{1,2}`-hop dismountable is not dismountable. -/
lemma not_dismountable_of_not_twoHopDismountable {H : Subgraph G}
    (h₀ : ¬H.TwoHopDismountable) : ¬H.Dismountable :=
  mt twoHopDismountable_of_dismountable h₀

/-- SAND 2025, Lemma 3.2: distinct vertices of `vplus` have distinct earliest neighbors. -/
lemma vplus_ne_neighbor_of_not_twoHopDismountable {H : Subgraph G} [H.IsSymm]
    {x y : V} (hx : x ∈ H.vplus) (hy : y ∈ H.vplus) (h₀ : ¬H.TwoHopDismountable)
    (h₁ : H.IsCliqueSubgraph) (h₂ : x ≠ y) :
    ∀ z z' : V, H.EarliestNeighbor x z ∧ H.EarliestNeighbor y z' → z ≠ z' := by
  simp only [EarliestNeighbor, ne_eq, and_imp, forall_exists_index]
  intro z z' n hee m hee' hzz'
  absurd h₀
  constructor ; assumption'
  by_cases ht : m ≤ n
  · use y
    constructor
    · apply Or.inr
      use x, z, n, m
      refine ⟨by simpa using h₂, hee, ?_, by assumption⟩
      grind only [= EarliestEdge.eq_1, → TemporalGraph.adj_symm]
    · apply Or.inl ; assumption
  · use x
    constructor
    · apply Or.inr
      use y, z', m, n
      refine ⟨by simpa using h₂.symm, hee', ?_, by omega⟩
      grind only [= EarliestEdge.eq_1, → TemporalGraph.adj_symm]
    · apply Or.inl ; assumption

/-- SAND 2025, Lemma 3.2: distinct vertices of `vminus` have distinct latest neighbors. -/
lemma vminus_ne_neighbor_of_not_twoHopDismountable {H : Subgraph G} [H.IsSymm]
    {x y : V} (hx : x ∈ H.vminus) (hy : y ∈ H.vminus) (h₀ : ¬H.TwoHopDismountable)
    (h₁ : H.IsCliqueSubgraph) (h₂ : x ≠ y) :
    ∀ z z' : V, H.LatestNeighbor x z ∧ H.LatestNeighbor y z' → z ≠ z' := by
  simp only [LatestNeighbor, ne_eq, and_imp, forall_exists_index]
  intro z z' n hle m hle' hzz'
  absurd h₀
  constructor ; assumption'
  by_cases ht : n ≤ m
  · use y
    constructor
    · apply Or.inl ; assumption
    · apply Or.inr
      use x, z, n, m
      refine ⟨by simpa using h₂, hle, ?_, by assumption⟩
      grind only [= LatestEdge.eq_1, → TemporalGraph.adj_symm]
  · use x
    constructor
    · apply Or.inl ; assumption
    · apply Or.inr
      use y, z', m, n
      refine ⟨by simpa using h₂.symm, hle', ?_, by omega⟩
      grind only [= LatestEdge.eq_1, → TemporalGraph.adj_symm]

/-- Earliest side of two-hop dismountability: one or two edges of `H` such that, in any `K`
between them and `H`, whatever is reachable from `y` is reachable from `x`. -/
lemma exists_edgeSet_of_earliest {H : Subgraph G} [G.IsSymm] [G.IsLoopless] [H.IsSymm] {x : V}
    (h₀ : (∃ y : V, H.EarliestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.EarliestEdge y z n ∧ H.Adj z x m ∧ m ≤ n)) :
    ∃ y ∈ H.verts, y ≠ x ∧ ∃ E : Set (Sym2 V × ℕ), E ⊆ H.edgeSet ∧ E.ncard ≤ 2 ∧
      x ∈ (Subgraph.fromEdgeSet G E).verts ∧
      ∀ (K : Subgraph G) [K.IsSymm], Subgraph.fromEdgeSet G E ≤ K → K ≤ H →
        ∀ b, K.Reachable y b → K.Reachable x b := by
  rcases h₀ with ⟨y, n, hE⟩ | ⟨y, z, n, m, hyx, hE, hzx, hmn⟩
  · -- one hop: the earliest edge `y x`
    have hadj : H.Adj y x n := hE.left
    refine ⟨y, H.edge_vert hadj, hadj.ne, {(s(y, x), n)}, ?_, ?_,
      ⟨⟨(s(y, x), n), rfl⟩, Sym2.mem_mk_right _ _⟩, ?_⟩
    · exact Set.singleton_subset_iff.mpr (H.mem_edgeSet.mpr hadj)
    · rw [Set.ncard_singleton]; omega
    · intro K _ hK hKH b
      exact reachable_of_earliestEdge
        (earliestEdge_of_ge hKH hE (adj_of_fromEdgeSet_le hK rfl (H.adj_sub hadj))) b
  · -- two hops: the earliest edge `y z`, then the edge `z x`
    have hyz : H.Adj y z n := hE.left
    refine ⟨y, H.edge_vert hyz, hyx, {(s(y, z), n), (s(z, x), m)}, ?_,
      ncard_pair_le _ _, ⟨⟨(s(z, x), m), by simp⟩, Sym2.mem_mk_right _ _⟩, ?_⟩
    · exact Set.insert_subset (H.mem_edgeSet.mpr hyz)
        (Set.singleton_subset_iff.mpr (H.mem_edgeSet.mpr hzx))
    · intro K _ hK hKH b
      have hKyz : K.Adj y z n := adj_of_fromEdgeSet_le hK (by simp) (H.adj_sub hyz)
      have hzx' : K.Adj z x m := adj_of_fromEdgeSet_le hK (by simp) (H.adj_sub hzx)
      exact reachable_of_extended_earliestEdge (earliestEdge_of_ge hKH hE hKyz) hzx'.symm hmn b

/-- Latest side of two-hop dismountability: one or two edges of `H` such that, in any `K`
between them and `H`, whatever reaches `y` reaches `x`. -/
lemma exists_edgeSet_of_latest {H : Subgraph G} [G.IsSymm] [G.IsLoopless] [H.IsSymm] {x : V}
    (h₀ : (∃ y : V, H.LatestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.LatestEdge y z n ∧ H.Adj z x m ∧ n ≤ m)) :
    ∃ y ∈ H.verts, y ≠ x ∧ ∃ E : Set (Sym2 V × ℕ), E ⊆ H.edgeSet ∧ E.ncard ≤ 2 ∧
      x ∈ (Subgraph.fromEdgeSet G E).verts ∧
      ∀ (K : Subgraph G) [K.IsSymm], Subgraph.fromEdgeSet G E ≤ K → K ≤ H →
        ∀ b, K.Reachable b y → K.Reachable b x := by
  rcases h₀ with ⟨y, n, hE⟩ | ⟨y, z, n, m, hyx, hE, hzx, hmn⟩
  · -- one hop: the latest edge `y x`
    have hadj : H.Adj y x n := hE.left
    refine ⟨y, H.edge_vert hadj, hadj.ne, {(s(y, x), n)}, ?_, ?_,
      ⟨⟨(s(y, x), n), rfl⟩, Sym2.mem_mk_right _ _⟩, ?_⟩
    · exact Set.singleton_subset_iff.mpr (H.mem_edgeSet.mpr hadj)
    · rw [Set.ncard_singleton]; omega
    · intro K _ hK hKH b
      exact reachable_of_latestEdge
        (latestEdge_of_ge hKH hE (adj_of_fromEdgeSet_le hK rfl (H.adj_sub hadj))) b
  · -- two hops: the latest edge `y z`, then the edge `z x`
    have hyz : H.Adj y z n := hE.left
    refine ⟨y, H.edge_vert hyz, hyx, {(s(y, z), n), (s(z, x), m)}, ?_,
      ncard_pair_le _ _, ⟨⟨(s(z, x), m), by simp⟩, Sym2.mem_mk_right _ _⟩, ?_⟩
    · exact Set.insert_subset (H.mem_edgeSet.mpr hyz)
        (Set.singleton_subset_iff.mpr (H.mem_edgeSet.mpr hzx))
    · intro K _ hK hKH b
      have hKyz : K.Adj y z n := adj_of_fromEdgeSet_le hK (by simp) (H.adj_sub hyz)
      have hzx' : K.Adj z x m := adj_of_fromEdgeSet_le hK (by simp) (H.adj_sub hzx)
      exact reachable_of_extended_latestEdge (latestEdge_of_ge hKH hE hKyz) hzx' hmn b

end TwoHop

section NeighborFunctions

/-- Every vertex of a finite, nontrivial, simple clique subgraph has an earliest incident
edge. -/
lemma earliestEdge_exists_of_finite_nontrivial_simple_clique {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) :
    ∀ x ∈ H.verts, ∃ (y : V) (n : ℕ), H.EarliestEdge x y n := by
  intro x hx
  have his₀ : (H.incidenceSet x).Nonempty :=
    nonempty_incidenceSet_of_nontrivial_clique h₁ x hx
  have his₁ : (H.incidenceSet x).Finite := finite_incidenceSet_of_finite_simple h₀ x
  exact earliestEdge_exists_of_nonempty_finite_incidenceSet his₀ his₁

/-- Every vertex of a finite, nontrivial, simple clique subgraph has a latest incident
edge. -/
lemma latestEdge_exists_of_finite_nontrivial_simple_clique {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) :
    ∀ x ∈ H.verts, ∃ (y : V) (n : ℕ), H.LatestEdge x y n := by
  intro x hx
  have his₀ : (H.incidenceSet x).Nonempty :=
    nonempty_incidenceSet_of_nontrivial_clique h₁ x hx
  have his₁ : (H.incidenceSet x).Finite := finite_incidenceSet_of_finite_simple h₀ x
  exact latestEdge_exists_of_nonempty_finite_incidenceSet his₀ his₁

/-- Every vertex of a finite, nontrivial, simple, proper clique subgraph has a unique earliest
incident edge. -/
lemma earliestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ x ∈ H.verts, ∃! q : V × ℕ, H.EarliestEdge x q.1 q.2 := by
  intro x hx
  have ⟨y, n, h⟩ := earliestEdge_exists_of_finite_nontrivial_simple_clique h₀ h₁ x hx
  use ⟨y, n⟩
  constructor
  · simp [h]
  · intro ⟨z, m⟩ h'
    simp only [Prod.mk.injEq]
    -- both are earliest edges at `x`, so `n = m`; properness then gives `z = y`
    grind only [= IsProper.eq_1, = EarliestEdge.eq_1]

/-- Every vertex of a finite, nontrivial, simple, proper clique subgraph has a unique latest
incident edge. -/
lemma latestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ x ∈ H.verts, ∃! q : V × ℕ, H.LatestEdge x q.1 q.2 := by
  intro x hx
  have ⟨y, n, h⟩ := latestEdge_exists_of_finite_nontrivial_simple_clique h₀ h₁ x hx
  use ⟨y, n⟩
  constructor
  · simp [h]
  · intro ⟨z, m⟩ h'
    simp only [Prod.mk.injEq]
    -- both are latest edges at `x`, so `n = m`; properness then gives `z = y`
    grind only [= IsProper.eq_1, = LatestEdge.eq_1]

/-- Every vertex of `H.verts`, in a finite, nontrivial, simple, proper clique subgraph, has a
unique earliest neighbor. -/
lemma existsUnique_earliestNeighbor {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ x ∈ H.verts, ∃! y, H.EarliestNeighbor x y := by
  intro x hx
  obtain ⟨⟨y, n⟩, hee, hunique⟩ :=
    earliestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique h₀ h₁ h₂ x hx
  refine ⟨y, ⟨n, hee⟩, ?_⟩
  intro z ⟨m, hee'⟩
  exact congrArg Prod.fst (hunique ⟨z, m⟩ hee')

/-- `EarliestNeighbor` witnesses membership in `vminus`. -/
lemma earliestNeighbor_mem_vminus {H : Subgraph G} {x y : V} (h : H.EarliestNeighbor x y) :
    y ∈ H.vminus :=
  ⟨x, h⟩

/-- Every vertex of `H.verts`, in a finite, nontrivial, simple, proper clique subgraph, has a
unique latest neighbor. -/
lemma existsUnique_latestNeighbor {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ x ∈ H.verts, ∃! y, H.LatestNeighbor x y := by
  intro x hx
  obtain ⟨⟨y, n⟩, hle, hunique⟩ :=
    latestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique h₀ h₁ h₂ x hx
  refine ⟨y, ⟨n, hle⟩, ?_⟩
  intro z ⟨m, hle'⟩
  exact congrArg Prod.fst (hunique ⟨z, m⟩ hle')

/-- `LatestNeighbor` witnesses membership in `vplus`. -/
lemma latestNeighbor_mem_vplus {H : Subgraph G} {x y : V} (h : H.LatestNeighbor x y) :
    y ∈ H.vplus :=
  ⟨x, h⟩

/-- The earliest-neighbor function on `V`, sending `x ∈ H.verts` to its unique earliest neighbor
(see `existsUnique_earliestNeighbor`) and left at `x` outside `H.verts`. Restricted to `vplus`, it
lands in `vminus` (`earliestNeighborFn_mapsTo`). -/
noncomputable def earliestNeighborFn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    V → V := by
  classical
  exact fun x ↦
    if hx : x ∈ H.verts then
      (existsUnique_earliestNeighbor h₀ h₁ h₂ x hx).exists.choose
    else x

/-- Characterizes `earliestNeighborFn` in terms of `EarliestNeighbor`, at a vertex of `H.verts`. -/
lemma earliestNeighborFn_eq {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] {x y : V}
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) (h₃ : x ∈ H.verts) :
    earliestNeighborFn h₀ h₁ h₂ x = y ↔ H.EarliestNeighbor x y := by
  unfold earliestNeighborFn
  rw [dite_eq_left h₃]
  constructor
  · intro h
    rw [← h]
    exact (existsUnique_earliestNeighbor h₀ h₁ h₂ x h₃).exists.choose_spec
  · exact (existsUnique_earliestNeighbor h₀ h₁ h₂ x h₃).unique
      (existsUnique_earliestNeighbor h₀ h₁ h₂ x h₃).exists.choose_spec

/-- `earliestNeighborFn` sends `vplus` into `vminus`. -/
lemma earliestNeighborFn_mapsTo {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    Set.MapsTo (earliestNeighborFn h₀ h₁ h₂) H.vplus H.vminus := by
  intro x hx
  exact earliestNeighbor_mem_vminus
    ((earliestNeighborFn_eq h₀ h₁ h₂ (vplus_sub_verts hx)).mp rfl)

/-- `earliestNeighborFn` is injective on `vplus` when `H` is a finite, nontrivial, simple, proper
clique that is not `{1,2}`-hop dismountable (used to build the `vminus`/`vplus` bijection). -/
lemma earliestNeighborFn_injOn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Set.InjOn (earliestNeighborFn h₀ h₁ h₂) H.vplus := by
  intro x hx y hy hfeq
  by_contra hne
  have hz : H.EarliestNeighbor x (earliestNeighborFn h₀ h₁ h₂ y) := by
    rw [← hfeq]
    exact (earliestNeighborFn_eq h₀ h₁ h₂ (vplus_sub_verts hx)).mp rfl
  have hz' : H.EarliestNeighbor y (earliestNeighborFn h₀ h₁ h₂ y) :=
    (earliestNeighborFn_eq h₀ h₁ h₂ (vplus_sub_verts hy)).mp rfl
  exact (vplus_ne_neighbor_of_not_twoHopDismountable hx hy h₃ h₁ hne _ _ ⟨hz, hz'⟩) rfl

/-- `vplus` has at most as many elements as `vminus`, via injectivity of `earliestNeighborFn`. -/
lemma vplus_card_le_vminus_card {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    H.vplus.ncard ≤ H.vminus.ncard :=
  Set.ncard_le_ncard_of_injOn (earliestNeighborFn h₀ h₁ h₂)
    (earliestNeighborFn_mapsTo h₀ h₁ h₂) (earliestNeighborFn_injOn h₀ h₁ h₂ h₃)

/-- The latest-neighbor function on `V`, sending `x ∈ H.verts` to its unique latest neighbor
(see `existsUnique_latestNeighbor`) and left at `x` outside `H.verts`. Restricted to `vminus`, it
lands in `vplus` (`latestNeighborFn_mapsTo`). -/
noncomputable def latestNeighborFn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    V → V := by
  classical
  exact fun x ↦
    if hx : x ∈ H.verts then
      (existsUnique_latestNeighbor h₀ h₁ h₂ x hx).exists.choose
    else x

/-- Characterizes `latestNeighborFn` in terms of `LatestNeighbor`, at a vertex of `H.verts`. -/
lemma latestNeighborFn_eq {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] {x y : V}
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) (h₃ : x ∈ H.verts) :
    latestNeighborFn h₀ h₁ h₂ x = y ↔ H.LatestNeighbor x y := by
  unfold latestNeighborFn
  rw [dite_eq_left h₃]
  constructor
  · intro h
    rw [← h]
    exact (existsUnique_latestNeighbor h₀ h₁ h₂ x h₃).exists.choose_spec
  · exact (existsUnique_latestNeighbor h₀ h₁ h₂ x h₃).unique
      (existsUnique_latestNeighbor h₀ h₁ h₂ x h₃).exists.choose_spec

/-- `latestNeighborFn` sends `vminus` into `vplus`. -/
lemma latestNeighborFn_mapsTo {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    Set.MapsTo (latestNeighborFn h₀ h₁ h₂) H.vminus H.vplus := by
  intro x hx
  exact latestNeighbor_mem_vplus
    ((latestNeighborFn_eq h₀ h₁ h₂ (vminus_sub_verts hx)).mp rfl)

/-- `latestNeighborFn` is injective on `vminus` when `H` is a finite, nontrivial, simple, proper
clique that is not `{1,2}`-hop dismountable (used to build the `vminus`/`vplus` bijection). -/
lemma latestNeighborFn_injOn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Set.InjOn (latestNeighborFn h₀ h₁ h₂) H.vminus := by
  intro x hx y hy hfeq
  by_contra hne
  have hz : H.LatestNeighbor x (latestNeighborFn h₀ h₁ h₂ y) := by
    rw [← hfeq]
    exact (latestNeighborFn_eq h₀ h₁ h₂ (vminus_sub_verts hx)).mp rfl
  have hz' : H.LatestNeighbor y (latestNeighborFn h₀ h₁ h₂ y) :=
    (latestNeighborFn_eq h₀ h₁ h₂ (vminus_sub_verts hy)).mp rfl
  exact (vminus_ne_neighbor_of_not_twoHopDismountable hx hy h₃ h₁ hne _ _ ⟨hz, hz'⟩) rfl

/-- `vminus` has at most as many elements as `vplus`, via injectivity of `latestNeighborFn`. -/
lemma vminus_card_le_vplus_card {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    H.vminus.ncard ≤ H.vplus.ncard :=
  Set.ncard_le_ncard_of_injOn (latestNeighborFn h₀ h₁ h₂)
    (latestNeighborFn_mapsTo h₀ h₁ h₂) (latestNeighborFn_injOn h₀ h₁ h₂ h₃)

/-- SAND 2025, Corollary 3.3 (3): `vminus` and `vplus` have the same cardinality. -/
lemma vminus_card_eq_vplus_card {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    H.vminus.ncard = H.vplus.ncard :=
  le_antisymm (vminus_card_le_vplus_card h₀ h₁ h₂ h₃) (vplus_card_le_vminus_card h₀ h₁ h₂ h₃)

/-- SAND 2025, Corollary 3.3 (via Lemma 3.2): `earliestNeighborFn` gives a bijection between the
sets `vplus` and `vminus`. -/
lemma earliestNeighborFn_bijOn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Set.BijOn (earliestNeighborFn h₀ h₁ h₂) H.vplus H.vminus := by
  have hinj := earliestNeighborFn_injOn h₀ h₁ h₂ h₃
  have himg : earliestNeighborFn h₀ h₁ h₂ '' H.vplus = H.vminus := by
    apply Set.eq_of_subset_of_ncard_le (earliestNeighborFn_mapsTo h₀ h₁ h₂).image_subset
    rw [hinj.ncard_image]
    exact (vminus_card_eq_vplus_card h₀ h₁ h₂ h₃).le
  exact himg ▸ hinj.bijOn_image

/-- SAND 2025, Corollary 3.3 (via Lemma 3.2): `latestNeighborFn` gives a bijection between the
sets `vminus` and `vplus`. -/
lemma latestNeighborFn_bijOn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    Set.BijOn (latestNeighborFn h₀ h₁ h₂) H.vminus H.vplus := by
  have hinj := latestNeighborFn_injOn h₀ h₁ h₂ h₃
  have himg : latestNeighborFn h₀ h₁ h₂ '' H.vminus = H.vplus := by
    apply Set.eq_of_subset_of_ncard_le (latestNeighborFn_mapsTo h₀ h₁ h₂).image_subset
    rw [hinj.ncard_image]
    exact (vminus_card_eq_vplus_card h₀ h₁ h₂ h₃).ge
  exact himg ▸ hinj.bijOn_image

/-- SAND 2025, Corollary 3.3 (1): `{e⁻(v) : v ∈ V⁺}` is a perfect matching, i.e. every vertex of
`vminus` has a unique earliest edge from a vertex of `vplus`. -/
lemma existsUnique_vplus_earliestEdge {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    ∀ x ∈ H.vminus, ∃! q : V × ℕ, q.1 ∈ H.vplus ∧ H.EarliestEdge q.1 x q.2 := by
  intro x hx
  have hbij := earliestNeighborFn_bijOn h₀ h₁ h₂ h₃
  obtain ⟨y, hy, hfy⟩ := hbij.surjOn hx
  obtain ⟨n, hee⟩ := (earliestNeighborFn_eq h₀ h₁ h₂ (vplus_sub_verts hy)).mp hfy
  refine ⟨⟨y, n⟩, ⟨hy, hee⟩, ?_⟩
  rintro ⟨z, m⟩ ⟨hz, hee'⟩
  have hfz : earliestNeighborFn h₀ h₁ h₂ z = x :=
    (earliestNeighborFn_eq h₀ h₁ h₂ (vplus_sub_verts hz)).mpr ⟨m, hee'⟩
  have heqv : z = y := hbij.injOn hz hy (hfz.trans hfy.symm)
  -- `z = y`, so simplicity forces the two times to agree
  grind only [= IsSimple.eq_1, = EarliestEdge.eq_1]

/-- SAND 2025, Corollary 3.3 (2): `{e⁺(v) : v ∈ V⁻}` is a perfect matching, i.e. every vertex of
`vplus` has a unique latest edge from a vertex of `vminus`. -/
lemma existsUnique_vminus_latestEdge {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    ∀ x ∈ H.vplus, ∃! q : V × ℕ, q.1 ∈ H.vminus ∧ H.LatestEdge q.1 x q.2 := by
  intro x hx
  have hbij := latestNeighborFn_bijOn h₀ h₁ h₂ h₃
  obtain ⟨y, hy, hfy⟩ := hbij.surjOn hx
  obtain ⟨n, hle⟩ := (latestNeighborFn_eq h₀ h₁ h₂ (vminus_sub_verts hy)).mp hfy
  refine ⟨⟨y, n⟩, ⟨hy, hle⟩, ?_⟩
  rintro ⟨z, m⟩ ⟨hz, hle'⟩
  have hfz : latestNeighborFn h₀ h₁ h₂ z = x :=
    (latestNeighborFn_eq h₀ h₁ h₂ (vminus_sub_verts hz)).mpr ⟨m, hle'⟩
  have heqv : z = y := hbij.injOn hz hy (hfz.trans hfy.symm)
  -- `z = y`, so simplicity forces the two times to agree
  grind only [= IsSimple.eq_1, = LatestEdge.eq_1]

end NeighborFunctions

section VzeroEmpty

/-- SAND 2025, Lemma 3.4: in a clique that is not `{1,2}`-hop dismountable, `V⁰ = ∅`. -/
lemma vzero_empty_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    H.vzero = ∅ := by
  by_contra! ⟨x, hx⟩
  have ⟨y, n, hee⟩ :=
    earliestEdge_exists_of_finite_nontrivial_simple_clique h₀ h₁ x (vzero_sub_verts hx)
  have hyin : y ∈ H.vminus := ⟨x, ⟨n, hee⟩⟩
  have ⟨z, m, hle⟩ :=
    latestEdge_exists_of_finite_nontrivial_simple_clique h₀ h₁ x (vzero_sub_verts hx)
  have hzin : z ∈ H.vplus := ⟨x, ⟨m, hle⟩⟩
  -- Here call SAND 2025 Corollary 3.3 to define y' ∈ H.vplus with y it's earliest neighbor
  -- symm for z' ∈ H.vminus with z it's latest neighbor
  have ⟨⟨y', n'⟩, ⟨hy'in, hee'⟩, _⟩ := existsUnique_vplus_earliestEdge h₀ h₁ h₂ h₃ y hyin
  have ⟨⟨z', m'⟩, ⟨hz'in, hle'⟩, _⟩ := existsUnique_vminus_latestEdge h₀ h₁ h₂ h₃ z hzin
  by_cases hlt : n' ≤ n
  <;> absurd h₃
  · constructor
    · trivial
    · use y'
      have ⟨⟨y'', _⟩, ⟨_, hle''⟩, _⟩ := existsUnique_vminus_latestEdge h₀ h₁ h₂ h₃ y' hy'in
      refine ⟨?_, Or.inl ⟨y'', ⟨_, hle''⟩⟩⟩
      apply Or.inr
      use x, y, n, n'
      refine ⟨?_, hee, H.adj_symm hee'.left, hlt⟩
      intro heq
      absurd hy'in
      rw [heq] at hx
      exact (vzero_mem y' hx).right
  · constructor
    · trivial
    · by_cases hlt' : m ≤ m'
      · -- Same as above with z and hee instead of y and hle
        use z'
        have ⟨⟨z'', _⟩, ⟨_, hee''⟩, _⟩ := existsUnique_vplus_earliestEdge h₀ h₁ h₂ h₃ z' hz'in
        refine ⟨Or.inl ⟨z'', ⟨_, hee''⟩⟩, ?_⟩
        apply Or.inr
        use x, z, m, m'
        refine ⟨?_, hle, H.adj_symm hle'.left, hlt'⟩
        intro heq
        absurd hz'in
        rw [heq] at hx
        exact (vzero_mem z' hx).left
      · use x
        constructor
        <;> apply Or.inr
        · use y', y, n' , n
          refine ⟨?_, hee', H.adj_symm hee.left, Nat.le_of_not_le hlt⟩
          intro heq
          absurd hy'in
          rw [←heq] at hx
          exact (vzero_mem y' hx).right
        · use z', z, m', m
          refine ⟨?_, hle', H.adj_symm hle.left, Nat.le_of_not_le hlt'⟩
          intro heq
          absurd hz'in
          rw [←heq] at hx
          exact (vzero_mem z' hx).left

end VzeroEmpty

section Reciprocity

/-- SAND 2025, Lemma 3.5 (Reciprocity), first statement: if `v u` occurs at time `n` as `v`'s
earliest edge, every edge from `u` to a vertex of `vplus` occurs no earlier than `n`. -/
lemma earliestEdge_reciprocity {H : Subgraph G} [H.IsSymm] {u v : V} {n : ℕ}
    (h₀ : H.IsCliqueSubgraph) (h₁ : ¬H.TwoHopDismountable) (h₂ : H.EarliestEdge v u n) :
    ∀ w ∈ H.vplus, ∀ j, H.Adj u w j → n ≤ j := by
  intro w hw j hj
  by_contra! hlt
  -- `w` reaches `v` in two hops, through `u` then `e⁻(v)`; and `w ∈ V⁺`
  refine h₁ ⟨h₀, w, Or.inr ⟨v, u, n, j, ?_, h₂, hj, hlt.le⟩, Or.inl hw⟩
  rintro rfl
  exact absurd (h₂.2 u j hj.symm) (by omega)

/-- SAND 2025, Lemma 3.5 (Reciprocity), second statement: if `u v` occurs at time `n` as `u`'s
latest edge, every edge from `v` to a vertex of `vminus` occurs no later than `n`. -/
lemma latestEdge_reciprocity {H : Subgraph G} [H.IsSymm] {u v : V} {n : ℕ}
    (h₀ : H.IsCliqueSubgraph) (h₁ : ¬H.TwoHopDismountable) (h₂ : H.LatestEdge u v n) :
    ∀ w ∈ H.vminus, ∀ j, H.Adj v w j → j ≤ n := by
  intro w hw j hj
  by_contra! hlt
  -- `w ∈ V⁻`; and `u` reaches `w` in two hops, through `e⁺(u)` then `v`
  refine h₁ ⟨h₀, w, Or.inl hw, Or.inr ⟨u, v, n, j, ?_, h₂, hj, hlt.le⟩⟩
  rintro rfl
  exact absurd (h₂.2 v j hj.symm) (by omega)

end Reciprocity

section biclique

/-- SAND 2025, Corollary 4.1: when `H` is not `{1,2}`-hop dismountable, the bipartite subgraph
between `vminus` and `vplus` is a bi-clique on those two sets. -/
lemma biclique_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsCliqueSubgraph) (h₁ : ¬H.TwoHopDismountable) :
    (H.between H.vminus H.vplus).IsBicliqueWith H.vminus H.vplus := by
  refine IsClique.between_isBicliqueWith h₀ vminus_sub_verts vplus_sub_verts ?_
  -- a vertex in both `V⁻` and `V⁺` would make `H` dismountable (Lemma 3.1)
  exact Set.disjoint_left.mpr fun x hm hp ↦ not_dismountable_of_not_twoHopDismountable h₁
    ((nonempty_vplus_inter_vminus_iff_dismountable H).mp ⟨h₀, x, hp, hm⟩)

/-- SAND 2025, remark after Corollary 4.1: the bi-clique between `vminus` and `vplus` is always
temporally connected. -/
lemma between_TC_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    (H.between H.vminus H.vplus).TemporallyConnectedSubgraph := by
  set K := H.between H.vminus H.vplus
  have hbc : K.IsBicliqueWith H.vminus H.vplus := biclique_of_not_twoHopDismountable h₁ h₃
  have hmem : ∀ v ∈ H.verts, v ∈ H.vminus ∨ v ∈ H.vplus := by
    intro v hv
    by_contra hc
    push Not at hc
    have hz : v ∈ H.vzero := ⟨hv, by simp [hc.1, hc.2]⟩
    rw [vzero_empty_of_not_twoHopDismountable h₀ h₁ h₂ h₃] at hz
    exact hz
  -- an edge across the bi-clique, in both directions
  have hdirect : ∀ v w, v ∈ H.vminus → w ∈ H.vplus →
      K.toTemporalGraph.Reachable v w ∧ K.toTemporalGraph.Reachable w v := by
    intro v w hv hw
    obtain ⟨n, hn⟩ := hbc.adj_of_mem hv hw
    exact ⟨reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨.Single hn⟩⟩,
      reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨.Single hn.symm⟩⟩⟩
  intro x hx y hy
  rcases hmem x hx with hxm | hxp <;> rcases hmem y hy with hym | hyp
  · -- both in `V⁻`: through the vertex of `V⁺` whose earliest edge goes to `x`
    obtain ⟨⟨p, n⟩, ⟨hp, hpe⟩, -⟩ := existsUnique_vplus_earliestEdge h₀ h₁ h₂ h₃ x hxm
    have hKe : K.toTemporalGraph.EarliestEdge p x n :=
      ⟨⟨hpe.1, Or.inr ⟨hp, hxm⟩⟩, fun z j hz ↦ hpe.2 z j hz.1⟩
    exact TemporalGraph.reachable_of_earliestEdge hKe y (hdirect y p hym hp).2
  · exact (hdirect x y hxm hyp).1
  · exact (hdirect y x hym hxp).2
  · -- both in `V⁺`: through the vertex of `V⁻` whose latest edge goes to `y`
    obtain ⟨⟨a, n⟩, ⟨ha, hal⟩, -⟩ := existsUnique_vminus_latestEdge h₀ h₁ h₂ h₃ y hyp
    have hKl : K.toTemporalGraph.LatestEdge a y n :=
      ⟨⟨hal.1, Or.inl ⟨ha, hyp⟩⟩, fun z j hz ↦ hal.2 z j hz.1⟩
    exact TemporalGraph.reachable_of_latestEdge hKl x (hdirect a x ha hxp).2


end biclique

end Subgraph

section MatchingConnectivity

/-- `t` reaches `t` when every vertex of `t` is the endpoint of the earliest edge of some vertex
of `s`, and `s` reaches `t`: leave `b ∈ t` along that earliest edge, then follow `s → t`. -/
lemma reachable_of_earliestEdge_matching {G : TemporalGraph V} [G.IsSymm] {s t : Set V}
    (h₀ : ∀ b ∈ t, ∃ v ∈ s, ∃ n, G.EarliestEdge v b n)
    (h₁ : ∀ x ∈ s, ∀ y ∈ t, G.Reachable x y) :
    ∀ a ∈ t, ∀ b ∈ t, G.Reachable a b := by
  intro a ha b hb
  obtain ⟨v, hv, n, hvn⟩ := h₀ a ha
  exact reachable_of_earliestEdge hvn b (h₁ v hv b hb)

/-- `s` reaches `s` when every vertex of `s` is the endpoint of the latest edge of some vertex of
`t`, and `s` reaches `t`: follow `s → t`, then extend along that latest edge. -/
lemma reachable_of_latestEdge_matching {G : TemporalGraph V} [G.IsSymm] {s t : Set V}
    (h₀ : ∀ y ∈ s, ∃ b ∈ t, ∃ n, G.LatestEdge b y n)
    (h₁ : ∀ x ∈ s, ∀ y ∈ t, G.Reachable x y) :
    ∀ x ∈ s, ∀ y ∈ s, G.Reachable x y := by
  intro x hx y hy
  obtain ⟨b, hb, n, hbn⟩ := h₀ y hy
  exact reachable_of_latestEdge hbn x (h₁ x hx b hb)

/-- SAND 2025, §4.1 (after Corollary 4.1): if every vertex of `t` (playing `V⁻`) is the endpoint
of the earliest edge of a vertex of `s` (the matching `M⁻`), every vertex of `s` (playing `V⁺`) is
the endpoint of the latest edge of a vertex of `t` (the matching `M⁺`), and `s` reaches `t`, then
`s ∪ t` is temporally connected. -/
theorem temporallyConnected_of_reachable_of_matchings {G : TemporalGraph V} [G.IsSymm]
    {s t : Set V}
    (h₀ : ∀ b ∈ t, ∃ v ∈ s, ∃ n, G.EarliestEdge v b n)
    (h₁ : ∀ y ∈ s, ∃ b ∈ t, ∃ n, G.LatestEdge b y n)
    (h₂ : ∀ x ∈ s, ∀ y ∈ t, G.Reachable x y) :
    G.TemporallyConnected (s ∪ t) := by
  rintro x (hx | hx) y (hy | hy)
  · exact reachable_of_latestEdge_matching h₁ h₂ x hx y hy
  · exact h₂ x hx y hy
  · -- `x ∈ t` leaves along its `M⁻` edge to some `v ∈ s`, then `s` reaches `s`
    obtain ⟨v, hv, n, hvn⟩ := h₀ x hx
    exact reachable_of_earliestEdge hvn y (reachable_of_latestEdge_matching h₁ h₂ v hv y hy)
  · exact reachable_of_earliestEdge_matching h₀ h₂ x hx y hy

end MatchingConnectivity

end TemporalGraph
