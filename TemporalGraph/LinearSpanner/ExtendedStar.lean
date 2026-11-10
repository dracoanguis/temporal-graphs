/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.LinearSpanner.Stars

import TemporalGraph.Helpers.SetCard
import Mathlib.Data.Fintype.Lattice

/-!
# Extended stars of an extremally matched bi-clique

Baligács 2026, §4, on a subgraph `H` that is an extremally matched temporal bi-clique with sources
`s` and targets `t`. The extended stars `Ext(c)` (Definition 12, in `LinearSpanner/Stars.lean`)
span a subgraph `Subgraph.fromEdgeSet G (H.extStarSource s t c ∪ H.extStarTarget s t c')` of `H`,
and "`Ext(c)` reaches `y` from `x`" is read as reachability in this subgraph.

The labelings are not built (see `LinearSpanner/Stars.lean`, which also defines the vocabulary
`pos_x(z) ≤ pos_x(c)`, early/upper source and late target used below), and every `N_min`, `N_max`
is a vertex variable with a hypothesis `H.earliestNeighborFn v = some w`. The times are read on
the adjacency, and a comparison is the existence of times, `∃ k, H.Adj a b k ∧ ∃ l, H.Adj c d l ∧
k ≤ l`, which is false when an arc is missing; in a simple graph each arc has one time.

## Main results

* `TemporalGraph.IsExtremallyMatched.ncard_sourceExtendEdges_le`,
  `TemporalGraph.IsExtremallyMatched.ncard_targetExtendEdges_le` : in a simple proper graph, at
  most one extend edge per source (resp. target).
* `TemporalGraph.IsExtremallyMatched.ncard_extStar_union_le` : `Ext(c) ∪ Ext(c')` has at most
  `6n` edges, `n = |s| = |t|`.
* `TemporalGraph.IsExtremallyMatched.reachable_extStarSource`,
  `TemporalGraph.IsExtremallyMatched.reachable_extStarTarget` : Baligács 2026, Lemma 13.
* `TemporalGraph.IsExtremallyMatched.le_of_not_reachable_extStarSource`,
  `TemporalGraph.IsExtremallyMatched.le_of_not_reachable_extStarTarget` : Baligács 2026,
  Lemma 14.
* `TemporalGraph.IsExtremallyMatched.chain_of_not_reachable` : Baligács 2026, Corollary 15.
* `TemporalGraph.IsExtremallyMatched.isCutCrossing_or_reachable` : Baligács 2026, Lemma 16.

## References

* Júlia Baligács, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156v1 (2026), §4.
-/

@[expose] public section

universe u

namespace TemporalGraph

variable {V : Type u} {G : TemporalGraph V} {s t : Set V}

section Auxiliary

/-- For a nonempty finite set of vertices, each related by `r` to some time, some vertex has a
greatest time: each time of each vertex is at most some time of it. -/
private theorem exists_max_of_forall_exists {S : Set V} (r : V → ℕ → Prop) (h₀ : S.Finite)
    (h₁ : S.Nonempty) (h₂ : ∀ y ∈ S, ∃ n, r y n) :
    ∃ u ∈ S, ∀ y ∈ S, ∃ a, r y a ∧ ∃ b, r u b ∧ a ≤ b := by
  have : Finite S := h₀.to_subtype
  have : Nonempty S := h₁.to_subtype
  choose g hg using fun y : S ↦ h₂ y.1 y.2
  obtain ⟨u, hu⟩ := Finite.exists_max g
  exact ⟨u.1, u.2, fun y hy ↦ ⟨g ⟨y, hy⟩, hg ⟨y, hy⟩, g u, hg u, hu ⟨y, hy⟩⟩⟩

/-- For a nonempty finite set of vertices, each related by `r` to some time, some vertex has a
least time. -/
private theorem exists_min_of_forall_exists {S : Set V} (r : V → ℕ → Prop) (h₀ : S.Finite)
    (h₁ : S.Nonempty) (h₂ : ∀ y ∈ S, ∃ n, r y n) :
    ∃ u ∈ S, ∀ y ∈ S, ∃ a, r u a ∧ ∃ b, r y b ∧ a ≤ b := by
  have : Finite S := h₀.to_subtype
  have : Nonempty S := h₁.to_subtype
  choose g hg using fun y : S ↦ h₂ y.1 y.2
  obtain ⟨u, hu⟩ := Finite.exists_min g
  exact ⟨u.1, u.2, fun y hy ↦ ⟨g u, hg u, g ⟨y, hy⟩, hg ⟨y, hy⟩, hu ⟨y, hy⟩⟩⟩

/-- An edge is in a set of edges if it is there with its endpoints swapped. -/
private theorem mem_of_mem_swap {A : Set (Sym2 V × ℕ)} {a b : V} {n : ℕ} (h₀ : (s(b, a), n) ∈ A) :
    (s(a, b), n) ∈ A := by
  rwa [Sym2.eq_swap]

section Inclusions

variable {c : V}

/-- `E_min` is in the extended star from a source. -/
private theorem eMin_subset_extStarSource : G.eMin s ⊆ G.extStarSource s t c :=
  fun _ he ↦ Or.inl (Or.inl (Or.inl he))

/-- `E_max` is in the extended star from a source. -/
private theorem eMax_subset_extStarSource : G.eMax s ⊆ G.extStarSource s t c :=
  fun _ he ↦ Or.inl (Or.inl (Or.inr he))

/-- The edges at the center `c` are in the extended star from a source `c`. -/
private theorem incidentEdges_subset_extStarSource : G.incidentEdges c t ⊆ G.extStarSource s t c :=
  fun _ he ↦ Or.inl (Or.inr he)

/-- The extend edges are in the extended star from a source. -/
private theorem sourceExtendEdges_subset_extStarSource :
    G.sourceExtendEdges s t c ⊆ G.extStarSource s t c :=
  fun _ he ↦ Or.inr he

/-- `E_min` is in the extended star from a target. -/
private theorem eMin_subset_extStarTarget : G.eMin s ⊆ G.extStarTarget s t c :=
  fun _ he ↦ Or.inl (Or.inl (Or.inl he))

/-- `E_max` is in the extended star from a target. -/
private theorem eMax_subset_extStarTarget : G.eMax s ⊆ G.extStarTarget s t c :=
  fun _ he ↦ Or.inl (Or.inl (Or.inr he))

/-- The edges at the center `c` are in the extended star from a target `c`. -/
private theorem incidentEdges_subset_extStarTarget : G.incidentEdges c s ⊆ G.extStarTarget s t c :=
  fun _ he ↦ Or.inl (Or.inr he)

/-- The extend edges are in the extended star from a target. -/
private theorem targetExtendEdges_subset_extStarTarget :
    G.targetExtendEdges s t c ⊆ G.extStarTarget s t c :=
  fun _ he ↦ Or.inr he

end Inclusions

/-- Two vertices `u`, `u'` whose arcs from `c` are each no later than the other have the same time,
hence are equal in a simple proper graph. -/
private theorem eq_of_le_of_le (h₀ : G.IsSimple) (h₁ : G.IsProper) {c u u' : V}
    (h₂ : ∃ a, G.Adj c u a ∧ ∃ b, G.Adj c u' b ∧ a ≤ b)
    (h₃ : ∃ a, G.Adj c u' a ∧ ∃ b, G.Adj c u b ∧ a ≤ b) : u = u' := by
  obtain ⟨a₁, ha₁, b₁, hb₁, h₄⟩ := h₂
  obtain ⟨a₂, ha₂, b₂, hb₂, h₅⟩ := h₃
  -- each arc has one time, and the times at `c` of `u` and `u'` are each at most the other
  obtain rfl : a₁ = b₂ := h₀ ha₁ hb₂
  obtain rfl : b₁ = a₂ := h₀ hb₁ ha₂
  -- `a₁ ≤ b₁ ≤ a₁`, so `a₁ = b₁`
  obtain rfl : a₁ = b₁ := by omega
  exact h₁ ha₁ hb₁

end Auxiliary

namespace IsExtremallyMatched

variable {H : Subgraph G} {c u u' v : V}

section ExtendEdges

/-- Baligács 2026, Definition 12 (a): the extend target of a source is unique. Two of them have
edges to `c` that are each no later than the other, so at the same time, which in a simple proper
graph forces them to be equal. -/
theorem isSourceExtendTarget_unique (h₀ : H.IsSimple) (h₁ : H.IsProper)
    (h₂ : H.IsSourceExtendTarget t c v u) (h₃ : H.IsSourceExtendTarget t c v u') : u = u' :=
  eq_of_le_of_le h₀ h₁ (h₃.2.2 u h₂.1 h₂.2.1) (h₂.2.2 u' h₃.1 h₃.2.1)

/-- Baligács 2026, Definition 12 (b): the extend source of a target is unique, as the extend
target of a source. -/
theorem isTargetExtendSource_unique (h₀ : H.IsSimple) (h₁ : H.IsProper)
    (h₂ : H.IsTargetExtendSource s c v u) (h₃ : H.IsTargetExtendSource s c v u') : u = u' :=
  eq_of_le_of_le h₀ h₁ (h₂.2.2 u' h₃.1 h₃.2.1) (h₃.2.2 u h₂.1 h₂.2.1)

/-- The extend edges of `Ext(c)` from a source `c` are finitely many, and at most one per
source. -/
private theorem finite_and_ncard_sourceExtendEdges_le [Finite H.verts]
    (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple) (h₁ : H.IsProper) :
    (H.sourceExtendEdges s t c).Finite ∧ (H.sourceExtendEdges s t c).ncard ≤ s.ncard := by
  refine Set.finite_and_ncard_le_of_functional
    (fun v e ↦ ∃ u, H.IsSourceExtendTarget t c v u ∧ ∃ n, H.Adj v u n ∧ e = (s(v, u), n))
    h.finite_left (fun _ he ↦ he) ?_
  rintro v e e' ⟨u, hu, n, hn, rfl⟩ ⟨u', hu', n', hn', rfl⟩
  obtain rfl := isSourceExtendTarget_unique h₀ h₁ hu hu'
  obtain rfl : n = n' := h₀ hn hn'
  rfl

/-- The extend edges of `Ext(c)` from a target `c` are finitely many, and at most one per
target. -/
private theorem finite_and_ncard_targetExtendEdges_le [Finite H.verts]
    (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple) (h₁ : H.IsProper) :
    (H.targetExtendEdges s t c).Finite ∧ (H.targetExtendEdges s t c).ncard ≤ t.ncard := by
  refine Set.finite_and_ncard_le_of_functional
    (fun v e ↦ ∃ u, H.IsTargetExtendSource s c v u ∧ ∃ n, H.Adj u v n ∧ e = (s(u, v), n))
    h.finite_right (fun _ he ↦ he) ?_
  rintro v e e' ⟨u, hu, n, hn, rfl⟩ ⟨u', hu', n', hn', rfl⟩
  obtain rfl := isTargetExtendSource_unique h₀ h₁ hu hu'
  obtain rfl : n = n' := h₀ hn hn'
  rfl

/-- There are finitely many extend edges of `Ext(c)` from a source `c`. -/
theorem finite_sourceExtendEdges [Finite H.verts] (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) : (H.sourceExtendEdges s t c).Finite :=
  (h.finite_and_ncard_sourceExtendEdges_le h₀ h₁).1

/-- There are finitely many extend edges of `Ext(c)` from a target `c`. -/
theorem finite_targetExtendEdges [Finite H.verts] (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) : (H.targetExtendEdges s t c).Finite :=
  (h.finite_and_ncard_targetExtendEdges_le h₀ h₁).1

/-- At most one extend edge per source: `Ext(c)`, `c` a source, has at most `|s|` extend edges. -/
theorem ncard_sourceExtendEdges_le [Finite H.verts] (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) : (H.sourceExtendEdges s t c).ncard ≤ s.ncard :=
  (h.finite_and_ncard_sourceExtendEdges_le h₀ h₁).2

/-- At most one extend edge per target: `Ext(c)`, `c` a target, has at most `|t|` extend edges. -/
theorem ncard_targetExtendEdges_le [Finite H.verts] (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) : (H.targetExtendEdges s t c).ncard ≤ t.ncard :=
  (h.finite_and_ncard_targetExtendEdges_le h₀ h₁).2

/-- Baligács 2026, Lemma 17 (proof): `Ext(c) ∪ Ext(c')`, for a source `c` and a target `c'`,
consists of six groups of at most `n = |s| = |t|` edges each: `E_min`, `E_max`, the edges at `c`,
the edges at `c'`, at most one extend edge per source and at most one per target. -/
theorem ncard_extStar_union_le [Finite H.verts] (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) {c c' : V} :
    (H.extStarSource s t c ∪ H.extStarTarget s t c').ncard ≤ 6 * s.ncard := by
  have h₂ := h.ncard_eq h₁
  -- the union of the two stars is the union of the six groups
  have h₃ : H.extStarSource s t c ∪ H.extStarTarget s t c' =
      H.eMin s ∪ H.eMax s ∪ H.incidentEdges c t ∪ H.incidentEdges c' s ∪
        H.sourceExtendEdges s t c ∪ H.targetExtendEdges s t c' := by
    ext e
    simp only [extStarSource, extStarTarget, Set.mem_union]
    tauto
  -- each group has at most `n` edges
  have b₁ := ncard_eMin_le h₀ h.finite_left
  have b₂ := ncard_eMax_le h₀ h.finite_left
  have b₃ := ncard_incidentEdges_le (x := c) h₀ h.finite_right
  have b₄ := ncard_incidentEdges_le (x := c') h₀ h.finite_left
  have b₅ := h.ncard_sourceExtendEdges_le h₀ h₁ (c := c)
  have b₆ := h.ncard_targetExtendEdges_le h₀ h₁ (c := c')
  -- the sizes of the five successive unions are bounded by the sum of the sizes of the parts
  have u₁ := Set.ncard_union_le (H.eMin s) (H.eMax s)
  have u₂ := Set.ncard_union_le (H.eMin s ∪ H.eMax s) (H.incidentEdges c t)
  have u₃ := Set.ncard_union_le (H.eMin s ∪ H.eMax s ∪ H.incidentEdges c t)
    (H.incidentEdges c' s)
  have u₄ := Set.ncard_union_le (H.eMin s ∪ H.eMax s ∪ H.incidentEdges c t ∪
    H.incidentEdges c' s) (H.sourceExtendEdges s t c)
  have u₅ := Set.ncard_union_le (H.eMin s ∪ H.eMax s ∪ H.incidentEdges c t ∪
    H.incidentEdges c' s ∪ H.sourceExtendEdges s t c) (H.targetExtendEdges s t c')
  rw [h₃]
  -- the six bounds `b₁ … b₆` (with `|t| = |s|`) and the five union bounds add up to `6 |s|`
  omega

end ExtendEdges

section Reachability

variable [H.IsSymm] {x z : V}

/-- Baligács 2026, Lemma 13 (a): in the `c`-ordered labeling of the targets, let `z = N_max(u')`
and let `u = tᵢ` be the extend index of `z`. For a source `v` with `x = N_min(v) = t_j`, `j ≤ i`,
`Ext(c)` reaches `u'` from `v`, through the temporal walk `(v, x, c, u, z, u')`. -/
theorem reachable_extStarSource (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple)
    (h₁ : H.IsProper) (h₂ : v ∈ s) (h₃ : u' ∈ t) (h₄ : H.earliestNeighborFn v = some x)
    (h₅ : H.latestNeighborFn u' = some z) (h₆ : H.IsSourceExtendTarget t c z u)
    (h₇ : ∃ k, H.Adj c x k ∧ ∃ l, H.Adj c u l ∧ k ≤ l) :
    (Subgraph.fromEdgeSet G (H.extStarSource s t c)).Reachable v u' := by
  obtain ⟨k, hk, l, hl, hkl⟩ := h₇
  have hx : x ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₂ h₄
  have hz : z ∈ s := h.mem_left_of_latestNeighborFn_eq_some h₃ h₅
  -- the arcs `v x`, `u' z`, and `u c`, `u z` from the extend index
  obtain ⟨a, ha, -⟩ := h.exists_earliestEdge_of_earliestNeighborFn_eq_some h₁ (.inl h₂) h₄
  obtain ⟨m, hm⟩ := h.exists_adj_right h₃ hz
  obtain ⟨a', ha', b', hb', hab'⟩ := h₆.2.1
  -- the arc `c u` has one time
  have hlb : l = a' := h₀ hl ha'.symm
  -- start at `v`
  have hv : (Subgraph.fromEdgeSet G (H.extStarSource s t c)).ReachableWithin v v 0 0 :=
    .refl v le_rfl
  -- `v → x`, an edge of `E_min`
  have hvx := hv.step_fromEdgeSet ha.1
    (eMin_subset_extStarSource (h.mem_eMin_of_mem_union h₁ (.inl h₂) h₄ ha.1)) (Nat.zero_le _)
  -- `x → c`, an edge at `c`; temporal since `{v, x}` is the earliest edge at `x`
  have hxc := hvx.step_fromEdgeSet hk.symm
    (mem_of_mem_swap (incidentEdges_subset_extStarSource (mem_incidentEdges hx hk)))
    (h.le_of_earliestNeighborFn_eq_some h₀ h₁ (.inl h₂) h₄ ha.1 hk.symm)
  -- `c → u`, an edge at `c`
  have hcu := hxc.step_fromEdgeSet hl
    (incidentEdges_subset_extStarSource (mem_incidentEdges h₆.1 hl)) hkl
  -- `u → z`, the extend edge of `z`; temporal by definition of the extend index (`l = a' < b'`)
  have huz := hcu.step_fromEdgeSet hb'
    (mem_of_mem_swap (sourceExtendEdges_subset_extStarSource ⟨z, hz, u, h₆, b', hb'.symm, rfl⟩))
    (hlb.trans_le hab'.le)
  -- `z → u'`, an edge of `E_max`; temporal since it is the latest edge at `z`
  have hzu' := huz.step_fromEdgeSet hm.symm
    (mem_of_mem_swap (eMax_subset_extStarSource (h.mem_eMax_of_mem_union h₁ (.inr h₃) h₅ hm)))
    (h.le_of_latestNeighborFn_eq_some h₀ h₁ (.inr h₃) h₅ hm hb'.symm)
  exact hzu'.reachable

/-- Baligács 2026, Lemma 13 (b): in the `c`-ordered labeling of the sources (by decreasing time at
`c`), let `x = N_min(v)` and let `u = sᵢ` be the extend index of `x`. For `z = N_max(u')` with
`z = s_j`, `j ≤ i`, `Ext(c)` reaches `u'` from `v`, through the temporal walk
`(v, x, u, c, z, u')`. -/
theorem reachable_extStarTarget (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple)
    (h₁ : H.IsProper) (h₂ : v ∈ s) (h₃ : u' ∈ t) (h₄ : H.earliestNeighborFn v = some x)
    (h₅ : H.latestNeighborFn u' = some z) (h₆ : H.IsTargetExtendSource s c x u)
    (h₇ : ∃ k, H.Adj c u k ∧ ∃ l, H.Adj c z l ∧ k ≤ l) :
    (Subgraph.fromEdgeSet G (H.extStarTarget s t c)).Reachable v u' := by
  obtain ⟨k, hk, l, hl, hkl⟩ := h₇
  have hx : x ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₂ h₄
  have hz : z ∈ s := h.mem_left_of_latestNeighborFn_eq_some h₃ h₅
  -- the arcs `v x`, `u' z`, and `u x`, `u c` from the extend index
  obtain ⟨a, ha, -⟩ := h.exists_earliestEdge_of_earliestNeighborFn_eq_some h₁ (.inl h₂) h₄
  obtain ⟨m, hm⟩ := h.exists_adj_right h₃ hz
  obtain ⟨a', ha', b', hb', hab'⟩ := h₆.2.1
  -- the arc `c u` has one time
  have hkb : k = b' := h₀ hk hb'.symm
  -- start at `v`
  have hv : (Subgraph.fromEdgeSet G (H.extStarTarget s t c)).ReachableWithin v v 0 0 :=
    .refl v le_rfl
  -- `v → x`, an edge of `E_min`
  have hvx := hv.step_fromEdgeSet ha.1
    (eMin_subset_extStarTarget (h.mem_eMin_of_mem_union h₁ (.inl h₂) h₄ ha.1)) (Nat.zero_le _)
  -- `x → u`, the extend edge of `x`; temporal since `{v, x}` is the earliest edge at `x`
  have hxu := hvx.step_fromEdgeSet ha'.symm
    (mem_of_mem_swap (targetExtendEdges_subset_extStarTarget ⟨x, hx, u, h₆, a', ha', rfl⟩))
    (h.le_of_earliestNeighborFn_eq_some h₀ h₁ (.inl h₂) h₄ ha.1 ha'.symm)
  -- `u → c`, an edge at `c`; temporal by definition of the extend index
  have huc := hxu.step_fromEdgeSet hb'
    (mem_of_mem_swap (incidentEdges_subset_extStarTarget (mem_incidentEdges h₆.1 hb'.symm)))
    hab'.le
  -- `c → z`, an edge at `c`; temporal since `b' = k ≤ l`
  have hcz := huc.step_fromEdgeSet hl
    (incidentEdges_subset_extStarTarget (mem_incidentEdges hz hl)) (hkb.symm.trans_le hkl)
  -- `z → u'`, an edge of `E_max`; temporal since it is the latest edge at `z`
  have hzu' := hcz.step_fromEdgeSet hm.symm
    (mem_of_mem_swap (eMax_subset_extStarTarget (h.mem_eMax_of_mem_union h₁ (.inr h₃) h₅ hm)))
    (h.le_of_latestNeighborFn_eq_some h₀ h₁ (.inr h₃) h₅ hm hl.symm)
  exact hzu'.reachable

end Reachability

section NotReachable

variable [Finite H.verts] [H.IsSymm] {x z : V}

/-- Baligács 2026, Lemma 14 (a): if `Ext(c)` does not reach `u'` from `v`, with `x = N_min(v)` and
`z = N_max(u')`, then `pos_x(z) ≤ pos_x(c)`: the edge `{x, z}` comes no later than the edge
`{x, c}`. -/
theorem le_of_not_reachable_extStarSource (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) (h₂ : c ∈ s) (h₃ : v ∈ s) (h₄ : u' ∈ t)
    (h₅ : H.earliestNeighborFn v = some x) (h₆ : H.latestNeighborFn u' = some z)
    (h₇ : ¬(Subgraph.fromEdgeSet G (H.extStarSource s t c)).Reachable v u') :
    ∃ k, H.Adj x z k ∧ ∃ l, H.Adj x c l ∧ k ≤ l := by
  by_contra hnot
  have hx : x ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₃ h₅
  have hz : z ∈ s := h.mem_left_of_latestNeighborFn_eq_some h₄ h₆
  obtain ⟨k, hk⟩ := h.exists_adj_right hx hz
  obtain ⟨l, hl⟩ := h.exists_adj_right hx h₂
  -- the negated conclusion says `{x, c}` comes strictly before `{x, z}`
  have hlk : l < k := lt_of_not_ge fun hkl ↦ hnot ⟨k, hk, l, hl, hkl⟩
  -- the targets `y` with `pos_y(c) < pos_y(z)`: a finite set, containing `x`
  have hxS : x ∈ {y ∈ t | ∃ a, H.Adj y c a ∧ ∃ b, H.Adj y z b ∧ a < b} :=
    ⟨hx, l, hl, k, hk, hlk⟩
  -- its last element `u` in the `c`-ordered labeling is the extend index of `z`
  obtain ⟨u, ⟨hu, hu₁⟩, hu₂⟩ := exists_max_of_forall_exists (H.Adj c)
    (h.finite_right.subset (Set.sep_subset _ _)) ⟨x, hxS⟩ fun y hy ↦ h.exists_adj_left h₂ hy.1
  -- so Lemma 13 (a) reaches `u'` from `v`, since `x` comes no later than `u`
  exact h₇ (h.reachable_extStarSource h₀ h₁ h₃ h₄ h₅ h₆
    ⟨hu, hu₁, fun y hy hy' ↦ hu₂ y ⟨hy, hy'⟩⟩ (hu₂ x hxS))

/-- Baligács 2026, Lemma 14 (b): if `Ext(c)` does not reach `u'` from `v`, with `c` a target,
`x = N_min(v)` and `z = N_max(u')`, then `pos_z(c) ≤ pos_z(x)`: the edge `{z, c}` comes no later
than the edge `{z, x}`. -/
theorem le_of_not_reachable_extStarTarget (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) (h₂ : c ∈ t) (h₃ : v ∈ s) (h₄ : u' ∈ t)
    (h₅ : H.earliestNeighborFn v = some x) (h₆ : H.latestNeighborFn u' = some z)
    (h₇ : ¬(Subgraph.fromEdgeSet G (H.extStarTarget s t c)).Reachable v u') :
    ∃ k, H.Adj z c k ∧ ∃ l, H.Adj z x l ∧ k ≤ l := by
  by_contra hnot
  have hx : x ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₃ h₅
  have hz : z ∈ s := h.mem_left_of_latestNeighborFn_eq_some h₄ h₆
  obtain ⟨k, hk⟩ := h.exists_adj_left hz h₂
  obtain ⟨l, hl⟩ := h.exists_adj_left hz hx
  -- the negated conclusion says `{z, x}` comes strictly before `{z, c}`
  have hlk : l < k := lt_of_not_ge fun hkl ↦ hnot ⟨k, hk, l, hl, hkl⟩
  -- the sources `y` with `pos_y(x) < pos_y(c)`: a finite set, containing `z`
  have hzS : z ∈ {y ∈ s | ∃ a, H.Adj y x a ∧ ∃ b, H.Adj y c b ∧ a < b} :=
    ⟨hz, l, hl, k, hk, hlk⟩
  -- its last element `u` in the `c`-ordered labeling is the extend index of `x`
  obtain ⟨u, ⟨hu, hu₁⟩, hu₂⟩ := exists_min_of_forall_exists (H.Adj c)
    (h.finite_left.subset (Set.sep_subset _ _)) ⟨z, hzS⟩ fun y hy ↦ h.exists_adj_right h₂ hy.1
  -- so Lemma 13 (b) reaches `u'` from `v`, since `z` comes no later than `u`
  exact h₇ (h.reachable_extStarTarget h₀ h₁ h₃ h₄ h₅ h₆
    ⟨hu, hu₁, fun y hy hy' ↦ hu₂ y ⟨hy, hy'⟩⟩ (hu₂ z hzS))

/-- Baligács 2026, Corollary 15: if `Ext(c) ∪ Ext(d)`, for a source `c` and a target `d`, does not
reach `u'` from `v`, with `x = N_min(v)` and `z = N_max(u')`, then the walk `(d, z, x, c)` is
temporal, that is `pos_z(d) ≤ pos_z(x)` and `pos_x(z) ≤ pos_x(c)`. (Its first junction, at `d`, is
the one of the walk `(N_min(d), d, z, x, c)`, temporal for free since `N_min(d)` is the earliest
neighbor of `d`.) -/
theorem chain_of_not_reachable (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple)
    (h₁ : H.IsProper) {d : V} (h₂ : c ∈ s) (h₃ : d ∈ t) (h₄ : v ∈ s) (h₅ : u' ∈ t)
    (h₆ : H.earliestNeighborFn v = some x) (h₇ : H.latestNeighborFn u' = some z)
    (h₈ : ¬(Subgraph.fromEdgeSet G (H.extStarSource s t c ∪ H.extStarTarget s t d)).Reachable
      v u') :
    (∃ a, H.Adj d z a ∧ ∃ b, H.Adj z x b ∧ a ≤ b) ∧
      ∃ a, H.Adj z x a ∧ ∃ b, H.Adj x c b ∧ a ≤ b := by
  -- neither extended star reaches `u'` from `v`
  have hjunction_x := h.le_of_not_reachable_extStarSource h₀ h₁ h₂ h₄ h₅ h₆ h₇ fun hr ↦
    h₈ (Reachable.mono (Subgraph.toTemporalGraph_le
      (Subgraph.fromEdgeSet_mono Set.subset_union_left)) hr)
  have hjunction_z := h.le_of_not_reachable_extStarTarget h₀ h₁ h₃ h₄ h₅ h₆ h₇ fun hr ↦
    h₈ (Reachable.mono (Subgraph.toTemporalGraph_le
      (Subgraph.fromEdgeSet_mono Set.subset_union_right)) hr)
  -- the junction at `x` is Lemma 14 (a), the one at `z` is Lemma 14 (b), read on the swapped arcs
  exact ⟨hjunction_z.imp fun _ h₉ ↦ ⟨h₉.1.symm, h₉.2⟩, hjunction_x.imp fun _ h₉ ↦ ⟨h₉.1.symm, h₉.2⟩⟩

/-- Baligács 2026, Lemma 16: in the `c`-ordered labeling cut at `k` (threshold `τ`), every upper
source `v = sᵢ` (`i > k`) either is 3-hop-`k`-cut-crossing, or `Ext(c) ∪ Ext(w)` reaches every
target from every early source `s_j` (`j ≤ k`). Here `w = tᵢ = N_min(v)`. If the reachability fails
at some `(s_j, y)`, Corollary 15 makes `(v, w, z, p, c)` a temporal walk, with `p = N_min(s_j)` and
`z = N_max(y)`, which is a 3-hop crossing. -/
theorem isCutCrossing_or_reachable (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple)
    (h₁ : H.IsProper) (h₂ : c ∈ s) (τ : ℕ) {w : V} (h₃ : v ∈ s)
    (h₄ : H.earliestNeighborFn v = some w) (h₅ : ∃ k, H.Adj c w k ∧ τ < k) :
    H.IsCutCrossing s c τ 3 v ∨
      ∀ x ∈ H.earlySources s c τ, ∀ y ∈ t,
        (Subgraph.fromEdgeSet G (H.extStarSource s t c ∪ H.extStarTarget s t w)).Reachable x y := by
  refine or_iff_not_imp_right.2 fun h₆ ↦ ?_
  -- some pair `(s_j, y)` with `j ≤ k` is not reached
  push Not at h₆
  obtain ⟨x, ⟨hx, p, hp, hxτ⟩, y, hy, h₇⟩ := h₆
  have hw : w ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₃ h₄
  obtain ⟨z, hz⟩ := h.exists_latestNeighborFn_eq_some (.inr hy)
  -- Corollary 15 with `d = N_min(v)`
  obtain ⟨⟨a₁, ha₁, b₁, hb₁, hdz⟩, ⟨a₂, ha₂, b₂, hb₂, hzx⟩⟩ :=
    h.chain_of_not_reachable h₀ h₁ h₂ hw hx hy (Option.mem_def.1 hp) hz h₇
  obtain ⟨n, hn, -⟩ := h.exists_earliestEdge_of_earliestNeighborFn_eq_some h₁ (.inl h₃) h₄
  -- the junction at `w` is temporal, since `{v, w}` is the earliest edge at `w`
  have hvw : n ≤ a₁ := h.le_of_earliestNeighborFn_eq_some h₀ h₁ (.inl h₃) h₄ hn.1 ha₁
  -- the 3-hop walk `(v, w, z, p)`, whose last edge `{z, p}` is at time `b₁`
  let hwalk := ((NonemptyTemporalWalk.single hn.1).step ha₁ hvw).step hb₁ hdz
  -- it ends no later than the edge `{p, c}`
  refine ⟨⟨w, Option.mem_def.2 h₄, h₅⟩, x, hx, p, hp, hxτ, n, b₁, .ofNonempty hwalk, le_rfl,
    b₂, hb₂, ?_⟩
  -- the arc `z p` has one time
  obtain rfl : a₂ = b₁ := h₀ ha₂ hb₁
  exact hzx

@[deprecated (since := "2026-11-10")]
alias arcTime_le_of_not_reachable_extStarSource := le_of_not_reachable_extStarSource

@[deprecated (since := "2026-11-10")]
alias arcTime_le_of_not_reachable_extStarTarget := le_of_not_reachable_extStarTarget

@[deprecated (since := "2026-11-10")]
alias arcTime_chain_of_not_reachable := chain_of_not_reachable

end NotReachable

end IsExtremallyMatched

end TemporalGraph
