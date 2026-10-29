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

This module formalizes the structure of temporal cliques that are not dismountable, following
Carnevale, Casteigts & Corsini (SAND 2025, §§2–3), after Casteigts, Peters & Schoeters (CPS,
ICALP 2019 / JCSS). It underlies the `O(n log n)` spanner bound for temporal cliques and the
linear `7n` bound of `LinearSpanner/`: a clique with no `{1,2}`-hop dismountable vertex is
structured enough (earliest/latest neighbor bijections, `vzero = ∅`, reciprocity) to be reduced to
a bi-clique. The operations (`dismount`, `mount`, `twoHopMount`) that carry out the induction are
in `Dismountability/Operations.lean`.

A subgraph `H` partitions its vertices into `vminus` (vertices that are someone's earliest
neighbor), `vplus` (vertices that are someone's latest neighbor) and `vzero` (neither). `H` is
`Dismountable` when it is a clique with a vertex that is both an earliest and a latest neighbor;
`TwoHopDismountable` weakens this to allow reaching such a vertex within two hops. When `H` is not
two-hop-dismountable, the earliest/latest neighbor relations become bijections between `vminus`
and `vplus` (`earliestNeighborFn`, `latestNeighborFn`), which forces `vzero` to be empty.

## Main definitions

* `TemporalGraph.Subgraph.Dismountable` : SAND 2025, §2, 1-hop dismountability (the hypothesis of
  Theorem 2.1).
* `TemporalGraph.Subgraph.TwoHopDismountable` : SAND 2025, §2.1, `{1,2}`-hop dismountability
  (`k`-hop with `k ≤ 2`).
* `TemporalGraph.Subgraph.vminus`, `vplus`, `vzero` : SAND 2025, §3.1, `V⁻`/`V⁺`/`V⁰`, the
  partition of `H.verts` defined just before Lemma 3.1.
* `TemporalGraph.earliestNeighborFn`, `latestNeighborFn` : an earliest (resp. latest) neighbor
  of a vertex, as an `Option` (`none` when there is none); in a proper graph they characterize
  the earliest (resp. latest) neighbors (`earliestNeighborFn_eq_some_iff`) and exist exactly when
  an arc leaves the vertex (`earliestNeighborFn_eq_none_iff`, `exists_earliestNeighbor_iff`).

## Main results

* `TemporalGraph.Subgraph.partition_of_not_dismountable` : SAND 2025, Lemma 3.1.
* `TemporalGraph.Subgraph.vplus_ne_neighbor_of_not_twoHopDismountable`,
  `vminus_ne_neighbor_of_not_twoHopDismountable` : SAND 2025, Lemma 3.2.
* `TemporalGraph.Subgraph.existsUnique_vplus_earliestEdge`, `existsUnique_vminus_latestEdge`,
  `earliestNeighborFn_bijOn`, `latestNeighborFn_bijOn`, `vminus_card_eq_vplus_card` :
  SAND 2025, Corollary 3.3, perfect matchings and bijections between `vminus` and `vplus`
  (`Set.BijOn` from `vplus` onto `some '' vminus`, and conversely).
* `TemporalGraph.Subgraph.vzero_empty_of_not_twoHopDismountable` : SAND 2025, Lemma 3.4.
* `TemporalGraph.Subgraph.earliestEdge_reciprocity`, `latestEdge_reciprocity` : SAND 2025,
  Lemma 3.5 (Reciprocity).
* `TemporalGraph.Subgraph.biclique_of_not_twoHopDismountable` : SAND 2025, Corollary 4.1.
* `TemporalGraph.Subgraph.temporallyConnectedSubgraph_between_of_not_twoHopDismountable` :
  SAND 2025, remark after Corollary 4.1, the bi-clique between `vminus` and `vplus` is temporally
  connected.

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

section NeighborFunctions

variable {G : TemporalGraph V} {x y : V}

/-- The earliest-neighbor function: `some y` for an earliest neighbor `y` of `x` (the other end of
an earliest edge at `x`, unique in a proper graph: `earliestNeighborFn_eq_some`), and `none` when
`x` has no earliest neighbor, that is when no arc leaves `x` (`earliestNeighborFn_eq_none_iff`).
On a subgraph `H`, `H.earliestNeighborFn` sends `vplus` into `some '' vminus`
(`Subgraph.earliestNeighborFn_mapsTo`).

As for `arcTime`, `none` is an absence, not a vertex. To use the neighbor, first prove that it
exists, then unwrap: `(G.earliestNeighborFn x).get (earliestNeighborFn_isSome_iff.2 h)` with
`h : ∃ y, G.EarliestNeighbor x y` (`exists_earliestNeighbor_iff`: some arc leaves `x`), or work
with `G.earliestNeighborFn x = some y`. Never `Option.get!`/`Option.getD`, whose default is a
valid vertex. -/
noncomputable def earliestNeighborFn (G : TemporalGraph V) (x : V) : Option V := by
  classical
  exact if h : ∃ y, G.EarliestNeighbor x y then some h.choose else none

/-- The latest-neighbor function: `some y` for a latest neighbor `y` of `x` (unique in a proper
graph: `latestNeighborFn_eq_some`), and `none` when `x` has no latest neighbor: when no arc leaves
`x`, or when the times of the arcs leaving `x` are unbounded. As for `earliestNeighborFn`, prove
existence before unwrapping, `(G.latestNeighborFn x).get (latestNeighborFn_isSome_iff.2 h)`, or
work with `G.latestNeighborFn x = some y`; never a default. -/
noncomputable def latestNeighborFn (G : TemporalGraph V) (x : V) : Option V := by
  classical
  exact if h : ∃ y, G.LatestNeighbor x y then some h.choose else none

/-- `earliestNeighborFn x` is defined exactly when `x` has an earliest neighbor. -/
theorem earliestNeighborFn_isSome_iff :
    (G.earliestNeighborFn x).isSome ↔ ∃ y, G.EarliestNeighbor x y := by
  unfold earliestNeighborFn
  split_ifs with h <;> simp [h]

/-- `latestNeighborFn x` is defined exactly when `x` has a latest neighbor. -/
theorem latestNeighborFn_isSome_iff :
    (G.latestNeighborFn x).isSome ↔ ∃ y, G.LatestNeighbor x y := by
  unfold latestNeighborFn
  split_ifs with h <;> simp [h]

/-- A vertex has an earliest neighbor exactly when some arc leaves it: the times are natural
numbers, so the least of them exists. -/
theorem exists_earliestNeighbor_iff : (∃ y, G.EarliestNeighbor x y) ↔ ∃ y n, G.Adj x y n := by
  classical
  refine ⟨fun ⟨y, n, h₀, _⟩ ↦ ⟨y, n, h₀⟩, fun ⟨y, n, h₀⟩ ↦ ?_⟩
  -- the least time `k` of an arc leaving `x`
  have h₁ : ∃ k, ∃ z, G.Adj x z k := ⟨n, y, h₀⟩
  obtain ⟨z, h₂⟩ := Nat.find_spec h₁
  exact ⟨z, Nat.find h₁, h₂, fun w j h₃ ↦ Nat.find_min' h₁ ⟨w, h₃⟩⟩

/-- `earliestNeighborFn x` is `none` exactly when no arc leaves `x`. -/
theorem earliestNeighborFn_eq_none_iff : G.earliestNeighborFn x = none ↔ ∀ y n, ¬G.Adj x y n := by
  rw [← Option.not_isSome_iff_eq_none, earliestNeighborFn_isSome_iff, exists_earliestNeighbor_iff]
  simp only [not_exists]

/-- `latestNeighborFn x` is `none` exactly when `x` has no latest neighbor. -/
theorem latestNeighborFn_eq_none_iff :
    G.latestNeighborFn x = none ↔ ∀ y, ¬G.LatestNeighbor x y := by
  rw [← Option.not_isSome_iff_eq_none, latestNeighborFn_isSome_iff, not_exists]

/-- The value of `earliestNeighborFn x` is an earliest neighbor of `x`. -/
theorem earliestNeighbor_of_earliestNeighborFn_eq_some (h₀ : G.earliestNeighborFn x = some y) :
    G.EarliestNeighbor x y := by
  unfold earliestNeighborFn at h₀
  split_ifs at h₀ with h₁
  obtain rfl := Option.some.inj h₀
  exact h₁.choose_spec

/-- The value of `latestNeighborFn x` is a latest neighbor of `x`. -/
theorem latestNeighbor_of_latestNeighborFn_eq_some (h₀ : G.latestNeighborFn x = some y) :
    G.LatestNeighbor x y := by
  unfold latestNeighborFn at h₀
  split_ifs at h₀ with h₁
  obtain rfl := Option.some.inj h₀
  exact h₁.choose_spec

/-- In a proper graph, the earliest neighbor is unique: it is the value of `earliestNeighborFn x`.
Two earliest edges at `x` have the same time, and properness then forces the same endpoint. -/
@[grind →]
theorem earliestNeighborFn_eq_some (h₀ : G.IsProper) (h₁ : G.EarliestNeighbor x y) :
    G.earliestNeighborFn x = some y := by
  obtain ⟨z, h₂⟩ := Option.isSome_iff_exists.1 (earliestNeighborFn_isSome_iff.2 ⟨y, h₁⟩)
  obtain ⟨n, h₃, h₄⟩ := earliestNeighbor_of_earliestNeighborFn_eq_some h₂
  obtain ⟨m, h₅, h₆⟩ := h₁
  -- two earliest edges at `x` have the same time
  obtain rfl : n = m := le_antisymm (h₄ _ _ h₅) (h₆ _ _ h₃)
  rw [h₂, h₀ h₃ h₅]

/-- In a proper graph, the latest neighbor is unique: it is the value of `latestNeighborFn x`. -/
@[grind →]
theorem latestNeighborFn_eq_some (h₀ : G.IsProper) (h₁ : G.LatestNeighbor x y) :
    G.latestNeighborFn x = some y := by
  obtain ⟨z, h₂⟩ := Option.isSome_iff_exists.1 (latestNeighborFn_isSome_iff.2 ⟨y, h₁⟩)
  obtain ⟨n, h₃, h₄⟩ := latestNeighbor_of_latestNeighborFn_eq_some h₂
  obtain ⟨m, h₅, h₆⟩ := h₁
  -- two latest edges at `x` have the same time
  obtain rfl : n = m := le_antisymm (h₆ _ _ h₃) (h₄ _ _ h₅)
  rw [h₂, h₀ h₃ h₅]

/-- In a proper graph, `earliestNeighborFn` characterizes the earliest neighbors. -/
theorem earliestNeighborFn_eq_some_iff (h₀ : G.IsProper) :
    G.earliestNeighborFn x = some y ↔ G.EarliestNeighbor x y :=
  ⟨earliestNeighbor_of_earliestNeighborFn_eq_some, earliestNeighborFn_eq_some h₀⟩

/-- In a proper graph, `latestNeighborFn` characterizes the latest neighbors. -/
theorem latestNeighborFn_eq_some_iff (h₀ : G.IsProper) :
    G.latestNeighborFn x = some y ↔ G.LatestNeighbor x y :=
  ⟨latestNeighbor_of_latestNeighborFn_eq_some, latestNeighborFn_eq_some h₀⟩

/-- In a proper graph, the endpoint of an earliest edge at `x` is the value of
`earliestNeighborFn x`. This is the form `grind` can use as a forward rule from an earliest edge:
it unfolds `EarliestNeighbor`, so `earliestNeighborFn_eq_some` never fires on an `EarliestEdge`. -/
@[grind →]
theorem EarliestEdge.earliestNeighborFn_eq_some {n : ℕ} (h₀ : G.IsProper)
    (h₁ : G.EarliestEdge x y n) : G.earliestNeighborFn x = some y :=
  TemporalGraph.earliestNeighborFn_eq_some h₀ ⟨n, h₁⟩

/-- In a proper graph, the endpoint of a latest edge at `x` is the value of `latestNeighborFn x`.
-/
@[grind →]
theorem LatestEdge.latestNeighborFn_eq_some {n : ℕ} (h₀ : G.IsProper)
    (h₁ : G.LatestEdge x y n) : G.latestNeighborFn x = some y :=
  TemporalGraph.latestNeighborFn_eq_some h₀ ⟨n, h₁⟩

end NeighborFunctions

namespace Subgraph

variable {G : TemporalGraph V}

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
lemma vminus_subset_verts {H : Subgraph G} : H.vminus ⊆ H.verts := by
  intro x ⟨y, n, h, _⟩
  exact H.edge_vert' h

@[deprecated (since := "2026-10-29")]
alias vminus_sub_verts := vminus_subset_verts

instance {H : Subgraph G} [h : Finite H.verts] : Finite H.vminus :=
  Set.Finite.subset (H.verts.finite_coe_iff.mp h) vminus_subset_verts

/-- A (noncomputable) `Fintype` structure on `H.vminus`, from the `Finite` instance above; for
stating cardinalities with `Fintype.card`, not for computing. -/
noncomputable instance {H : Subgraph G} [Finite H.verts] : Fintype H.vminus :=
  Fintype.ofFinite _

/-- SAND 2025, §3.1: `V⁺`, defined before Lemma 3.1. The set of vertices that are someone's
latest neighbor. -/
def vplus (H : Subgraph G) : Set V := {x : V | ∃ y : V, H.LatestNeighbor y x}

/-- `H.vplus` is contained in `H.verts`. -/
@[simp]
lemma vplus_subset_verts {H : Subgraph G} : H.vplus ⊆ H.verts := by
  intro x ⟨y, n, h, _⟩
  exact H.edge_vert' h

@[deprecated (since := "2026-10-29")]
alias vplus_sub_verts := vplus_subset_verts

instance {H : Subgraph G} [h : Finite H.verts] : Finite H.vplus :=
  Set.Finite.subset (H.verts.finite_coe_iff.mp h) vplus_subset_verts

/-- A (noncomputable) `Fintype` structure on `H.vplus`, from the `Finite` instance above; for
stating cardinalities with `Fintype.card`, not for computing. -/
noncomputable instance {H : Subgraph G} [Finite H.verts] : Fintype H.vplus :=
  Fintype.ofFinite _

/-- SAND 2025, §3.1: `V⁰`, defined before Lemma 3.1. The vertices of `H` that are neither in
`vminus` nor `vplus`. -/
def vzero (H : Subgraph G) : Set V := H.verts \ (H.vminus ∪ H.vplus)

/-- `H.vzero` is contained in `H.verts`. -/
@[simp]
lemma vzero_subset_verts {H : Subgraph G} : H.vzero ⊆ H.verts := by
  intro x ⟨h, _⟩
  exact h

@[deprecated (since := "2026-10-29")]
alias vzero_sub_verts := vzero_subset_verts

instance {H : Subgraph G} [h : Finite H.verts] : Finite H.vzero :=
  Set.Finite.subset (H.verts.finite_coe_iff.mp h) vzero_subset_verts

/-- A (noncomputable) `Fintype` structure on `H.vzero`, from the `Finite` instance above; for
stating cardinalities with `Fintype.card`, not for computing. -/
noncomputable instance {H : Subgraph G} [Finite H.verts] : Fintype H.vzero :=
  Fintype.ofFinite _

/-- A vertex of `H.vzero` lies in neither `H.vminus` nor `H.vplus`. -/
lemma notMem_vminus_and_notMem_vplus_of_mem_vzero {H : Subgraph G} {x : V} (h₀ : x ∈ H.vzero) :
    x ∉ H.vminus ∧ x ∉ H.vplus := by
  simpa only [vzero, Set.mem_sdiff, Set.mem_union, not_or] using h₀.2

@[deprecated notMem_vminus_and_notMem_vplus_of_mem_vzero (since := "2026-10-29")]
lemma vzero_mem {H : Subgraph G} : ∀ x : V, x ∈ H.vzero → x ∉ H.vminus ∧ x ∉ H.vplus :=
  fun _ h₀ ↦ notMem_vminus_and_notMem_vplus_of_mem_vzero h₀

/-- `vminus`, `vplus` and `vzero` cover `H.verts`. -/
lemma vminus_union_vplus_union_vzero {H : Subgraph G} : H.vminus ∪ H.vplus ∪ H.vzero = H.verts := by
  simp [vzero]

@[deprecated (since := "2026-10-29")]
alias vunion_eq_univ := vminus_union_vplus_union_vzero

/-- `H` is a dismountable clique iff it is a clique and `H.vplus` and `H.vminus` intersect. -/
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
    exacts [rfl, absurd hs (hd hm), absurd hm (notMem_vminus_and_notMem_vplus_of_mem_vzero hs).1]
  by_cases hp : x ∈ H.vplus
  · refine ⟨H.vplus, ⟨by simp, hp⟩, ?_⟩
    rintro s ⟨(rfl | rfl | rfl), hs⟩
    exacts [absurd hs hm, rfl, absurd hp (notMem_vminus_and_notMem_vplus_of_mem_vzero hs).2]
  · refine ⟨H.vzero, ⟨by simp, hx, by simp [hm, hp]⟩, ?_⟩
    rintro s ⟨(rfl | rfl | rfl), hs⟩
    exacts [absurd hs hm, absurd hs hp, rfl]

end Partition

section TwoHop

/-- SAND 2025, §2.1: `{1,2}`-hop dismountability (`k`-hop, `k ≤ 2`). A clique subgraph `H` is
two-hop dismountable when some vertex `x` is reached within at most two hops both from an
earliest edge and from a latest edge. -/
def TwoHopDismountable (H : Subgraph G) :=
  H.IsCliqueSubgraph ∧ ∃ x : V,
    ((∃ y : V, H.EarliestNeighbor y x) ∨
      ∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.EarliestEdge y z n ∧ H.Adj z x m ∧ m ≤ n) ∧
    ((∃ y : V, H.LatestNeighbor y x) ∨
      ∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.LatestEdge y z n ∧ H.Adj z x m ∧ n ≤ m)

/-- A dismountable clique is `{1,2}`-hop dismountable. -/
lemma twoHopDismountable_of_dismountable {H : Subgraph G} (h : H.Dismountable) :
    H.TwoHopDismountable := by
  obtain ⟨hclique, x, y, z, hen, hln⟩ := h
  exact ⟨hclique, x, Or.inl ⟨y, hen⟩, Or.inl ⟨z, hln⟩⟩

/-- A subgraph that is not `{1,2}`-hop dismountable is not dismountable. -/
lemma not_dismountable_of_not_twoHopDismountable {H : Subgraph G}
    (h₀ : ¬H.TwoHopDismountable) : ¬H.Dismountable :=
  mt twoHopDismountable_of_dismountable h₀

/-- SAND 2025, Lemma 3.2: distinct vertices of `vplus` have distinct earliest neighbors.

If `x ≠ y` in `V⁺` shared the earliest neighbor `z`, comparing the times `n`, `m` of the earliest
edges `x z` and `y z` shows that `x` or `y` is `{1,2}`-hop dismountable. -/
lemma vplus_ne_neighbor_of_not_twoHopDismountable {H : Subgraph G} [H.IsSymm]
    {x y : V} (hx : x ∈ H.vplus) (hy : y ∈ H.vplus) (h₀ : ¬H.TwoHopDismountable)
    (h₁ : H.IsCliqueSubgraph) (h₂ : x ≠ y) :
    ∀ z z' : V, H.EarliestNeighbor x z ∧ H.EarliestNeighbor y z' → z ≠ z' := by
  simp only [EarliestNeighbor, ne_eq, and_imp, forall_exists_index]
  intro z z' n hee m hee' hzz'
  refine h₀ ⟨h₁, ?_⟩
  -- compare the times `n`, `m` of the two earliest edges `x z`, `y z`
  by_cases ht : m ≤ n
  · -- the vertex `y` is reached from `x` in two hops: the earliest edge `x z` (time `n`), then
    -- `z y` (time `m ≤ n`), and `y` is a latest neighbor
    refine ⟨y, Or.inr ⟨x, z, n, m, h₂, hee, ?_, ht⟩, Or.inl hy⟩
    -- the arc `y z` read backwards, `z = z'`
    grind only [= EarliestEdge.eq_1, → TemporalGraph.adj_symm]
  · -- symmetrically `x` is reached from `y` (so `n ≤ m`)
    refine ⟨x, Or.inr ⟨y, z', m, n, h₂.symm, hee', ?_, by omega⟩, Or.inl hx⟩
    -- the arc `x z'` read backwards, `z = z'`
    grind only [= EarliestEdge.eq_1, → TemporalGraph.adj_symm]

/-- SAND 2025, Lemma 3.2: distinct vertices of `vminus` have distinct latest neighbors.

Mirror image of `vplus_ne_neighbor_of_not_twoHopDismountable`. -/
lemma vminus_ne_neighbor_of_not_twoHopDismountable {H : Subgraph G} [H.IsSymm]
    {x y : V} (hx : x ∈ H.vminus) (hy : y ∈ H.vminus) (h₀ : ¬H.TwoHopDismountable)
    (h₁ : H.IsCliqueSubgraph) (h₂ : x ≠ y) :
    ∀ z z' : V, H.LatestNeighbor x z ∧ H.LatestNeighbor y z' → z ≠ z' := by
  simp only [LatestNeighbor, ne_eq, and_imp, forall_exists_index]
  intro z z' n hle m hle' hzz'
  refine h₀ ⟨h₁, ?_⟩
  by_cases ht : n ≤ m
  · -- the vertex `y` is reached from `x` in two hops: the latest edge `x z` (time `n`), then `z y`
    -- (time `m ≥ n`), and `y` is an earliest neighbor
    refine ⟨y, Or.inl hy, Or.inr ⟨x, z, n, m, h₂, hle, ?_, ht⟩⟩
    -- the arc `y z` read backwards, `z = z'`
    grind only [= LatestEdge.eq_1, → TemporalGraph.adj_symm]
  · -- symmetrically for `x` (so `m ≤ n`)
    refine ⟨x, Or.inl hx, Or.inr ⟨y, z', m, n, h₂.symm, hle', ?_, by omega⟩⟩
    -- the arc `x z'` read backwards, `z = z'`
    grind only [= LatestEdge.eq_1, → TemporalGraph.adj_symm]

end TwoHop

section Matchings

/-- Every vertex of a finite, nontrivial, simple clique subgraph has an earliest incident
edge. -/
lemma exists_earliestEdge_of_isCliqueSubgraph {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) :
    ∀ x ∈ H.verts, ∃ (y : V) (n : ℕ), H.EarliestEdge x y n := by
  intro x hx
  have his₀ : (H.incidenceSet x).Nonempty :=
    nonempty_incidenceSet_of_nontrivial_clique h₁ x hx
  have his₁ : (H.incidenceSet x).Finite := finite_incidenceSet_of_finite_simple h₀ x
  exact exists_earliestEdge_of_incidenceSet his₀ his₁

@[deprecated (since := "2026-10-29")]
alias earliestEdge_exists_of_finite_nontrivial_simple_clique :=
  exists_earliestEdge_of_isCliqueSubgraph

/-- Every vertex of a finite, nontrivial, simple clique subgraph has a latest incident
edge. -/
lemma exists_latestEdge_of_isCliqueSubgraph {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) :
    ∀ x ∈ H.verts, ∃ (y : V) (n : ℕ), H.LatestEdge x y n := by
  intro x hx
  have his₀ : (H.incidenceSet x).Nonempty :=
    nonempty_incidenceSet_of_nontrivial_clique h₁ x hx
  have his₁ : (H.incidenceSet x).Finite := finite_incidenceSet_of_finite_simple h₀ x
  exact exists_latestEdge_of_incidenceSet his₀ his₁

@[deprecated (since := "2026-10-29")]
alias latestEdge_exists_of_finite_nontrivial_simple_clique := exists_latestEdge_of_isCliqueSubgraph

/-- Every vertex of a finite, nontrivial, simple, proper clique subgraph has a unique earliest
incident edge. -/
lemma existsUnique_earliestEdge_of_isCliqueSubgraph {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ x ∈ H.verts, ∃! q : V × ℕ, H.EarliestEdge x q.1 q.2 := by
  intro x hx
  have ⟨y, n, h⟩ := exists_earliestEdge_of_isCliqueSubgraph h₀ h₁ x hx
  use ⟨y, n⟩
  constructor
  · simp [h]
  · intro ⟨z, m⟩ h'
    simp only [Prod.mk.injEq]
    -- both are earliest edges at `x`, so `n = m`; properness then gives `z = y`
    grind only [= IsProper.eq_1, = EarliestEdge.eq_1]

@[deprecated (since := "2026-10-29")]
alias earliestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique :=
  existsUnique_earliestEdge_of_isCliqueSubgraph

/-- Every vertex of a finite, nontrivial, simple, proper clique subgraph has a unique latest
incident edge. -/
lemma existsUnique_latestEdge_of_isCliqueSubgraph {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ x ∈ H.verts, ∃! q : V × ℕ, H.LatestEdge x q.1 q.2 := by
  intro x hx
  have ⟨y, n, h⟩ := exists_latestEdge_of_isCliqueSubgraph h₀ h₁ x hx
  use ⟨y, n⟩
  constructor
  · simp [h]
  · intro ⟨z, m⟩ h'
    simp only [Prod.mk.injEq]
    -- both are latest edges at `x`, so `n = m`; properness then gives `z = y`
    grind only [= IsProper.eq_1, = LatestEdge.eq_1]

@[deprecated (since := "2026-10-29")]
alias latestEdge_existsUnique_of_finite_nontrivial_simple_proper_clique :=
  existsUnique_latestEdge_of_isCliqueSubgraph

/-- Every vertex of `H.verts`, in a finite, nontrivial, simple, proper clique subgraph, has a
unique earliest neighbor. -/
lemma existsUnique_earliestNeighbor {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∀ x ∈ H.verts, ∃! y, H.EarliestNeighbor x y := by
  intro x hx
  obtain ⟨⟨y, n⟩, hee, hunique⟩ :=
    existsUnique_earliestEdge_of_isCliqueSubgraph h₀ h₁ h₂ x hx
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
    existsUnique_latestEdge_of_isCliqueSubgraph h₀ h₁ h₂ x hx
  refine ⟨y, ⟨n, hle⟩, ?_⟩
  intro z ⟨m, hle'⟩
  exact congrArg Prod.fst (hunique ⟨z, m⟩ hle')

/-- `LatestNeighbor` witnesses membership in `vplus`. -/
lemma latestNeighbor_mem_vplus {H : Subgraph G} {x y : V} (h : H.LatestNeighbor x y) :
    y ∈ H.vplus :=
  ⟨x, h⟩

/-- In a finite nontrivial simple clique subgraph, every vertex of `H.verts` has an earliest
neighbor, so `earliestNeighborFn` is defined on it. -/
lemma exists_earliestNeighborFn_eq_some {H : Subgraph G} [Finite H.verts] [Nontrivial H.verts]
    {x : V} (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : x ∈ H.verts) :
    ∃ y, H.earliestNeighborFn x = some y := by
  obtain ⟨y, n, h₃⟩ := exists_earliestEdge_of_isCliqueSubgraph h₀ h₁ x h₂
  exact Option.isSome_iff_exists.1 (earliestNeighborFn_isSome_iff.2 ⟨y, n, h₃⟩)

/-- `earliestNeighborFn` sends `vplus` into `vminus`: its values there are `some` of a vertex of
`vminus`. -/
lemma earliestNeighborFn_mapsTo {H : Subgraph G} [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) :
    Set.MapsTo H.earliestNeighborFn H.vplus (some '' H.vminus) := by
  intro x hx
  obtain ⟨y, h₂⟩ := exists_earliestNeighborFn_eq_some h₀ h₁ (vplus_subset_verts hx)
  exact ⟨y, earliestNeighbor_mem_vminus (earliestNeighbor_of_earliestNeighborFn_eq_some h₂),
    h₂.symm⟩

/-- `earliestNeighborFn` is injective on `vplus` when `H` is a finite, nontrivial, simple clique
that is not `{1,2}`-hop dismountable (used to build the `vminus`/`vplus` bijection). -/
lemma earliestNeighborFn_injOn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : ¬H.TwoHopDismountable) :
    Set.InjOn H.earliestNeighborFn H.vplus := by
  intro x hx y hy hfeq
  by_contra hne
  -- `x` and `y` would share their earliest neighbor `z` (SAND 2025, Lemma 3.2)
  obtain ⟨z, hz⟩ := exists_earliestNeighborFn_eq_some h₀ h₁ (vplus_subset_verts hy)
  exact (vplus_ne_neighbor_of_not_twoHopDismountable hx hy h₂ h₁ hne _ _
    ⟨earliestNeighbor_of_earliestNeighborFn_eq_some (hfeq.trans hz),
      earliestNeighbor_of_earliestNeighborFn_eq_some hz⟩) rfl

/-- `vplus` has at most as many elements as `vminus`, via injectivity of `earliestNeighborFn`. -/
lemma vplus_card_le_vminus_card {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : ¬H.TwoHopDismountable) :
    H.vplus.ncard ≤ H.vminus.ncard :=
  calc H.vplus.ncard ≤ (some '' H.vminus).ncard :=
        Set.ncard_le_ncard_of_injOn _ (earliestNeighborFn_mapsTo h₀ h₁)
          (earliestNeighborFn_injOn h₀ h₁ h₂)
    _ = H.vminus.ncard := Set.ncard_image_of_injective _ (Option.some_injective V)

/-- In a finite nontrivial simple clique subgraph, every vertex of `H.verts` has a latest
neighbor, so `latestNeighborFn` is defined on it. -/
lemma exists_latestNeighborFn_eq_some {H : Subgraph G} [Finite H.verts] [Nontrivial H.verts]
    {x : V} (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : x ∈ H.verts) :
    ∃ y, H.latestNeighborFn x = some y := by
  obtain ⟨y, n, h₃⟩ := exists_latestEdge_of_isCliqueSubgraph h₀ h₁ x h₂
  exact Option.isSome_iff_exists.1 (latestNeighborFn_isSome_iff.2 ⟨y, n, h₃⟩)

/-- `latestNeighborFn` sends `vminus` into `vplus`: its values there are `some` of a vertex of
`vplus`. -/
lemma latestNeighborFn_mapsTo {H : Subgraph G} [Finite H.verts] [Nontrivial H.verts]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) :
    Set.MapsTo H.latestNeighborFn H.vminus (some '' H.vplus) := by
  intro x hx
  obtain ⟨y, h₂⟩ := exists_latestNeighborFn_eq_some h₀ h₁ (vminus_subset_verts hx)
  exact ⟨y, latestNeighbor_mem_vplus (latestNeighbor_of_latestNeighborFn_eq_some h₂),
    h₂.symm⟩

/-- `latestNeighborFn` is injective on `vminus` when `H` is a finite, nontrivial, simple clique
that is not `{1,2}`-hop dismountable (used to build the `vplus`/`vminus` bijection). -/
lemma latestNeighborFn_injOn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : ¬H.TwoHopDismountable) :
    Set.InjOn H.latestNeighborFn H.vminus := by
  intro x hx y hy hfeq
  by_contra hne
  -- `x` and `y` would share their latest neighbor `z` (SAND 2025, Lemma 3.2)
  obtain ⟨z, hz⟩ := exists_latestNeighborFn_eq_some h₀ h₁ (vminus_subset_verts hy)
  exact (vminus_ne_neighbor_of_not_twoHopDismountable hx hy h₂ h₁ hne _ _
    ⟨latestNeighbor_of_latestNeighborFn_eq_some (hfeq.trans hz),
      latestNeighbor_of_latestNeighborFn_eq_some hz⟩) rfl

/-- `vminus` has at most as many elements as `vplus`, via injectivity of `latestNeighborFn`. -/
lemma vminus_card_le_vplus_card {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : ¬H.TwoHopDismountable) :
    H.vminus.ncard ≤ H.vplus.ncard :=
  calc H.vminus.ncard ≤ (some '' H.vplus).ncard :=
        Set.ncard_le_ncard_of_injOn _ (latestNeighborFn_mapsTo h₀ h₁)
          (latestNeighborFn_injOn h₀ h₁ h₂)
    _ = H.vplus.ncard := Set.ncard_image_of_injective _ (Option.some_injective V)

/-- SAND 2025, Corollary 3.3 (3): `vminus` and `vplus` have the same cardinality. -/
lemma vminus_card_eq_vplus_card {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : ¬H.TwoHopDismountable) :
    H.vminus.ncard = H.vplus.ncard :=
  le_antisymm (vminus_card_le_vplus_card h₀ h₁ h₂) (vplus_card_le_vminus_card h₀ h₁ h₂)

/-- SAND 2025, Corollary 3.3 (via Lemma 3.2): `earliestNeighborFn` gives a bijection between the
sets `vplus` and `vminus`. -/
lemma earliestNeighborFn_bijOn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : ¬H.TwoHopDismountable) :
    Set.BijOn H.earliestNeighborFn H.vplus (some '' H.vminus) := by
  have hinj := earliestNeighborFn_injOn h₀ h₁ h₂
  have himg : H.earliestNeighborFn '' H.vplus = some '' H.vminus := by
    apply Set.eq_of_subset_of_ncard_le (earliestNeighborFn_mapsTo h₀ h₁).image_subset
    rw [hinj.ncard_image, Set.ncard_image_of_injective _ (Option.some_injective V)]
    exact (vminus_card_eq_vplus_card h₀ h₁ h₂).le
  exact himg ▸ hinj.bijOn_image

/-- SAND 2025, Corollary 3.3 (via Lemma 3.2): `latestNeighborFn` gives a bijection between the
sets `vminus` and `vplus`. -/
lemma latestNeighborFn_bijOn {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : ¬H.TwoHopDismountable) :
    Set.BijOn H.latestNeighborFn H.vminus (some '' H.vplus) := by
  have hinj := latestNeighborFn_injOn h₀ h₁ h₂
  have himg : H.latestNeighborFn '' H.vminus = some '' H.vplus := by
    apply Set.eq_of_subset_of_ncard_le (latestNeighborFn_mapsTo h₀ h₁).image_subset
    rw [hinj.ncard_image, Set.ncard_image_of_injective _ (Option.some_injective V)]
    exact (vminus_card_eq_vplus_card h₀ h₁ h₂).ge
  exact himg ▸ hinj.bijOn_image

/-- SAND 2025, Corollary 3.3 (1): `{e⁻(v) : v ∈ V⁺}` is a perfect matching, i.e. every vertex of
`vminus` has a unique earliest edge from a vertex of `vplus`. -/
lemma existsUnique_vplus_earliestEdge {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    ∀ x ∈ H.vminus, ∃! q : V × ℕ, q.1 ∈ H.vplus ∧ H.EarliestEdge q.1 x q.2 := by
  intro x hx
  have hbij := earliestNeighborFn_bijOn h₀ h₁ h₃
  obtain ⟨y, hy, hfy⟩ := hbij.surjOn ⟨x, hx, rfl⟩
  obtain ⟨n, hee⟩ := earliestNeighbor_of_earliestNeighborFn_eq_some hfy
  refine ⟨⟨y, n⟩, ⟨hy, hee⟩, ?_⟩
  rintro ⟨z, m⟩ ⟨hz, hee'⟩
  have hfz : H.earliestNeighborFn z = some x := earliestNeighborFn_eq_some h₂ ⟨m, hee'⟩
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
  have hbij := latestNeighborFn_bijOn h₀ h₁ h₃
  obtain ⟨y, hy, hfy⟩ := hbij.surjOn ⟨x, hx, rfl⟩
  obtain ⟨n, hle⟩ := latestNeighbor_of_latestNeighborFn_eq_some hfy
  refine ⟨⟨y, n⟩, ⟨hy, hle⟩, ?_⟩
  rintro ⟨z, m⟩ ⟨hz, hle'⟩
  have hfz : H.latestNeighborFn z = some x := latestNeighborFn_eq_some h₂ ⟨m, hle'⟩
  have heqv : z = y := hbij.injOn hz hy (hfz.trans hfy.symm)
  -- `z = y`, so simplicity forces the two times to agree
  grind only [= IsSimple.eq_1, = LatestEdge.eq_1]

end Matchings

section VzeroEmpty

/-- Earliest side of `SAND 2025, Lemma 3.4`: a vertex `x ∈ V⁰` has an earliest edge `x y`, and `y`
(being in `V⁻`) is the earliest neighbor of some `y' ∈ V⁺` (Corollary 3.3 (1)); `y'` differs
from `x` since `x ∉ V⁺`. -/
private lemma exists_vplus_earliestEdge_of_mem_vzero {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) (h₃ : ¬H.TwoHopDismountable)
    {x : V} (hx : x ∈ H.vzero) :
    ∃ y' ∈ H.vplus, y' ≠ x ∧ ∃ (y : V) (n n' : ℕ),
      H.EarliestEdge x y n ∧ H.EarliestEdge y' y n' := by
  obtain ⟨y, n, hee⟩ :=
    exists_earliestEdge_of_isCliqueSubgraph h₀ h₁ x (vzero_subset_verts hx)
  obtain ⟨⟨y', n'⟩, ⟨hy'plus, hee'⟩, -⟩ :=
    existsUnique_vplus_earliestEdge h₀ h₁ h₂ h₃ y ⟨x, n, hee⟩
  refine ⟨y', hy'plus, ?_, y, n, n', hee, hee'⟩
  rintro rfl
  exact (notMem_vminus_and_notMem_vplus_of_mem_vzero hx).2 hy'plus

/-- Latest side of `SAND 2025, Lemma 3.4`: a vertex `x ∈ V⁰` has a latest edge `x z`, and `z`
(being in `V⁺`) is the latest neighbor of some `z' ∈ V⁻` (Corollary 3.3 (2)); `z'` differs from
`x` since `x ∉ V⁻`. -/
private lemma exists_vminus_latestEdge_of_mem_vzero {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) (h₃ : ¬H.TwoHopDismountable)
    {x : V} (hx : x ∈ H.vzero) :
    ∃ z' ∈ H.vminus, z' ≠ x ∧ ∃ (z : V) (m m' : ℕ),
      H.LatestEdge x z m ∧ H.LatestEdge z' z m' := by
  obtain ⟨z, m, hle⟩ :=
    exists_latestEdge_of_isCliqueSubgraph h₀ h₁ x (vzero_subset_verts hx)
  obtain ⟨⟨z', m'⟩, ⟨hz'minus, hle'⟩, -⟩ :=
    existsUnique_vminus_latestEdge h₀ h₁ h₂ h₃ z ⟨x, m, hle⟩
  refine ⟨z', hz'minus, ?_, z, m, m', hle, hle'⟩
  rintro rfl
  exact (notMem_vminus_and_notMem_vplus_of_mem_vzero hx).1 hz'minus

/-- SAND 2025, Lemma 3.4: in a clique that is not `{1,2}`-hop dismountable, `V⁰ = ∅`.

Proof of the paper: for `x ∈ V⁰` let `x y` (time `n`) be its earliest edge and `x z` (time `m`) its
latest edge; by Corollary 3.3, `y' y` (time `n'`) is the earliest edge of `y` from some `y' ∈ V⁺`
and `z' z` (time `m'`) the latest edge of `z` from some `z' ∈ V⁻`. If `n' ≤ n`, then `y'` is
`{1,2}`-hop dismountable (earliest side through `y`, latest side as a vertex of `V⁺`); symmetrically
`z'` if `m ≤ m'`; otherwise `x` itself is. -/
lemma vzero_empty_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper)
    (h₃ : ¬H.TwoHopDismountable) :
    H.vzero = ∅ := by
  by_contra! ⟨x, hx⟩
  obtain ⟨y', hy'plus, hy'x, y, n, n', hee, hee'⟩ :=
    exists_vplus_earliestEdge_of_mem_vzero h₀ h₁ h₂ h₃ hx
  obtain ⟨z', hz'minus, hz'x, z, m, m', hle, hle'⟩ :=
    exists_vminus_latestEdge_of_mem_vzero h₀ h₁ h₂ h₃ hx
  by_cases hn : n' ≤ n
  · -- `y'` is reached from `x` through `y` within two hops, and is a latest neighbor
    exact h₃ ⟨h₁, y', Or.inr ⟨x, y, n, n', hy'x.symm, hee, H.adj_symm hee'.left, hn⟩,
      Or.inl hy'plus⟩
  by_cases hm : m ≤ m'
  · -- `z'` is an earliest neighbor, and reaches `x` through `z` within two hops
    exact h₃ ⟨h₁, z', Or.inl hz'minus, Or.inr ⟨x, z, m, m', hz'x.symm, hle,
      H.adj_symm hle'.left, hm⟩⟩
  · -- `x` itself: through `y` on the earliest side, through `z` on the latest side
    exact h₃ ⟨h₁, x, Or.inr ⟨y', y, n', n, hy'x, hee', H.adj_symm hee.left, (not_le.1 hn).le⟩,
      Or.inr ⟨z', z, m', m, hz'x, hle', H.adj_symm hle.left, (not_le.1 hm).le⟩⟩

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

section Biclique

/-- SAND 2025, Corollary 4.1: when `H` is not `{1,2}`-hop dismountable, the bipartite subgraph
between `vminus` and `vplus` is a bi-clique on those two sets. -/
lemma biclique_of_not_twoHopDismountable {H : Subgraph G}
    (h₀ : H.IsCliqueSubgraph) (h₁ : ¬H.TwoHopDismountable) :
    (H.between H.vminus H.vplus).IsBicliqueWith H.vminus H.vplus := by
  refine IsClique.between_isBicliqueWith h₀ vminus_subset_verts vplus_subset_verts ?_
  -- a vertex in both `V⁻` and `V⁺` would make `H` dismountable (Lemma 3.1)
  exact Set.disjoint_left.mpr fun x hm hp ↦ not_dismountable_of_not_twoHopDismountable h₁
    ((nonempty_vplus_inter_vminus_iff_dismountable H).mp ⟨h₀, x, hp, hm⟩)

/-- SAND 2025, remark after Corollary 4.1: the bi-clique between `vminus` and `vplus` is always
temporally connected. -/
lemma temporallyConnectedSubgraph_between_of_not_twoHopDismountable {H : Subgraph G}
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
    exact Set.notMem_empty v hz
  -- an edge across the bi-clique, in both directions
  have hdirect : ∀ v w, v ∈ H.vminus → w ∈ H.vplus →
      K.toTemporalGraph.Reachable v w ∧ K.toTemporalGraph.Reachable w v := by
    intro v w hv hw
    obtain ⟨n, hn⟩ := hbc.adj_of_mem hv hw
    exact ⟨NonemptyTemporalWalk.reachable (.single hn),
      NonemptyTemporalWalk.reachable (.single hn.symm)⟩
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

@[deprecated (since := "2026-10-29")]
alias between_TC_of_not_twoHopDismountable :=
  temporallyConnectedSubgraph_between_of_not_twoHopDismountable

end Biclique

end Subgraph

end TemporalGraph
