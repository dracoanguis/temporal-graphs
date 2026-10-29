/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.LinearSpanner.Stars

import TemporalGraph.ForMathlib.SetCard
import Mathlib.Data.Fintype.Lattice

/-!
# Extended stars of an extremally matched bi-clique

Baligács 2026, §4, on a subgraph `H` that is an extremally matched temporal bi-clique with sources
`s` and targets `t`. The extended stars `Ext(c)` (Definition 12, in `LinearSpanner/Stars.lean`)
span a subgraph `Subgraph.fromEdgeSet G (H.extStarSource s t c ∪ H.extStarTarget s t c')` of `H`,
and "`Ext(c)` reaches `y` from `x`" is read as reachability in this subgraph.

The labelings are not built (see `LinearSpanner/Stars.lean`, which also defines the vocabulary
`pos_x(z) ≤ pos_x(c)`, early/upper source and late target used below), and every `N_min`, `N_max`
is a vertex variable with a hypothesis `H.earliestNeighborFn v = some w`. The times are the values
of `H.arcTime`, and a comparison is the existence of values, `∃ k ∈ H.arcTime a b,
∃ l ∈ H.arcTime c d, k ≤ l`, which is false on `none`.

## Main results

* `TemporalGraph.IsExtremallyMatched.ncard_sourceExtendEdges_le`,
  `TemporalGraph.IsExtremallyMatched.ncard_targetExtendEdges_le` : at most one extend edge per
  source (resp. target).
* `TemporalGraph.IsExtremallyMatched.ncard_extStar_union_le` : `Ext(c) ∪ Ext(c')` has at most
  `6n` edges, `n = |s| = |t|`.
* `TemporalGraph.IsExtremallyMatched.reachable_extStarSource`,
  `TemporalGraph.IsExtremallyMatched.reachable_extStarTarget` : Baligács 2026, Lemma 13.
* `TemporalGraph.IsExtremallyMatched.arcTime_le_of_not_reachable_extStarSource`,
  `TemporalGraph.IsExtremallyMatched.arcTime_le_of_not_reachable_extStarTarget` : Baligács 2026,
  Lemma 14.
* `TemporalGraph.IsExtremallyMatched.arcTime_chain_of_not_reachable` : Baligács 2026,
  Corollary 15.
* `TemporalGraph.IsExtremallyMatched.isCutCrossing_or_reachable` : Baligács 2026, Lemma 16.

## References

* Júlia Baligács, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156v1 (2026), §4.
-/

@[expose] public section

universe u

namespace TemporalGraph

variable {V : Type u} {G : TemporalGraph V} {s t : Set V}

section Auxiliary

/-- For a nonempty finite set of vertices whose `f`-values all exist, some vertex has a greatest
value. -/
private theorem exists_max_of_isSome {S : Set V} (f : V → Option ℕ) (h₀ : S.Finite)
    (h₁ : S.Nonempty) (h₂ : ∀ y ∈ S, ∃ n, f y = some n) :
    ∃ u ∈ S, ∀ y ∈ S, ∃ a ∈ f y, ∃ b ∈ f u, a ≤ b := by
  have : Finite S := h₀.to_subtype
  have : Nonempty S := h₁.to_subtype
  choose g hg using fun y : S ↦ h₂ y.1 y.2
  obtain ⟨u, hu⟩ := Finite.exists_max g
  exact ⟨u.1, u.2, fun y hy ↦ ⟨g ⟨y, hy⟩, hg ⟨y, hy⟩, g u, hg u, hu ⟨y, hy⟩⟩⟩

/-- For a nonempty finite set of vertices whose `f`-values all exist, some vertex has a least
value. -/
private theorem exists_min_of_isSome {S : Set V} (f : V → Option ℕ) (h₀ : S.Finite)
    (h₁ : S.Nonempty) (h₂ : ∀ y ∈ S, ∃ n, f y = some n) :
    ∃ u ∈ S, ∀ y ∈ S, ∃ a ∈ f u, ∃ b ∈ f y, a ≤ b := by
  have : Finite S := h₀.to_subtype
  have : Nonempty S := h₁.to_subtype
  choose g hg using fun y : S ↦ h₂ y.1 y.2
  obtain ⟨u, hu⟩ := Finite.exists_min g
  exact ⟨u.1, u.2, fun y hy ↦ ⟨g u, hg u, g ⟨y, hy⟩, hg ⟨y, hy⟩, hu ⟨y, hy⟩⟩⟩

/-- Extend a window-bounded walk of `Subgraph.fromEdgeSet G E` by the arc `y → z` of a subgraph
`H` of `G`, when the edge `{y, z}` of `E` is at the time of this arc. -/
private theorem ReachableWithin.step_fromEdgeSet {H : Subgraph G} {E : Set (Sym2 V × ℕ)}
    {x y z : V} {a b k : ℕ} (h₀ : (Subgraph.fromEdgeSet G E).ReachableWithin x y a b)
    (h₁ : H.arcTime y z = some k) (h₂ : (s(y, z), k) ∈ E) (h₃ : b ≤ k) :
    (Subgraph.fromEdgeSet G E).ReachableWithin x z a k :=
  h₀.step ⟨⟨_, h₂⟩, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _, rfl,
    H.adj_sub (adj_of_arcTime_eq_some h₁)⟩ h₃

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
hence are equal in a proper graph. -/
private theorem eq_of_arcTime_le_le (h₀ : G.IsProper) {c u u' : V}
    (h₁ : ∃ a ∈ G.arcTime c u, ∃ b ∈ G.arcTime c u', a ≤ b)
    (h₂ : ∃ a ∈ G.arcTime c u', ∃ b ∈ G.arcTime c u, a ≤ b) : u = u' := by
  obtain ⟨a₁, ha₁, b₁, hb₁, h₃⟩ := h₁
  obtain ⟨a₂, ha₂, b₂, hb₂, h₄⟩ := h₂
  -- the times at `c` of `u` and `u'` are each at most the other
  have e₁ : a₁ = b₂ := Option.mem_unique ha₁ hb₂
  have e₂ : b₁ = a₂ := Option.mem_unique hb₁ ha₂
  -- `a₁ ≤ b₁ = a₂ ≤ b₂ = a₁`, so `a₁ = b₁`
  obtain rfl : a₁ = b₁ := by omega
  exact eq_of_arcTime_eq_some h₀ ha₁ hb₁

end Auxiliary

namespace IsExtremallyMatched

variable {H : Subgraph G} {c u u' v : V}

section ExtendEdges

/-- Baligács 2026, Definition 12 (a): the extend target of a source is unique. Two of them have
edges to `c` that are each no later than the other, so at the same time, which in a proper graph
forces them to be equal. -/
theorem isSourceExtendTarget_unique (h₀ : H.IsProper) (h₁ : H.IsSourceExtendTarget t c v u)
    (h₂ : H.IsSourceExtendTarget t c v u') : u = u' :=
  eq_of_arcTime_le_le h₀ (h₂.2.2 u h₁.1 h₁.2.1) (h₁.2.2 u' h₂.1 h₂.2.1)

/-- Baligács 2026, Definition 12 (b): the extend source of a target is unique, as the extend
target of a source. -/
theorem isTargetExtendSource_unique (h₀ : H.IsProper) (h₁ : H.IsTargetExtendSource s c v u)
    (h₂ : H.IsTargetExtendSource s c v u') : u = u' :=
  eq_of_arcTime_le_le h₀ (h₁.2.2 u' h₂.1 h₂.2.1) (h₂.2.2 u h₁.1 h₁.2.1)

/-- The extend edges of `Ext(c)` from a source `c` are finitely many, and at most one per
source. -/
private theorem finite_and_ncard_sourceExtendEdges_le [Finite H.verts]
    (h : H.IsExtremallyMatched s t) (h₀ : H.IsProper) :
    (H.sourceExtendEdges s t c).Finite ∧ (H.sourceExtendEdges s t c).ncard ≤ s.ncard := by
  refine finite_and_ncard_le_of_functional
    (fun v e ↦ ∃ u, H.IsSourceExtendTarget t c v u ∧ ∃ n ∈ H.arcTime v u, e = (s(v, u), n))
    h.finite_left (fun _ he ↦ he) ?_
  rintro v e e' ⟨u, hu, n, hn, rfl⟩ ⟨u', hu', n', hn', rfl⟩
  obtain rfl := isSourceExtendTarget_unique h₀ hu hu'
  obtain rfl : n = n' := Option.mem_unique hn hn'
  rfl

/-- The extend edges of `Ext(c)` from a target `c` are finitely many, and at most one per
target. -/
private theorem finite_and_ncard_targetExtendEdges_le [Finite H.verts]
    (h : H.IsExtremallyMatched s t) (h₀ : H.IsProper) :
    (H.targetExtendEdges s t c).Finite ∧ (H.targetExtendEdges s t c).ncard ≤ t.ncard := by
  refine finite_and_ncard_le_of_functional
    (fun v e ↦ ∃ u, H.IsTargetExtendSource s c v u ∧ ∃ n ∈ H.arcTime u v, e = (s(u, v), n))
    h.finite_right (fun _ he ↦ he) ?_
  rintro v e e' ⟨u, hu, n, hn, rfl⟩ ⟨u', hu', n', hn', rfl⟩
  obtain rfl := isTargetExtendSource_unique h₀ hu hu'
  obtain rfl : n = n' := Option.mem_unique hn hn'
  rfl

/-- There are finitely many extend edges of `Ext(c)` from a source `c`. -/
theorem finite_sourceExtendEdges [Finite H.verts] (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsProper) : (H.sourceExtendEdges s t c).Finite :=
  (h.finite_and_ncard_sourceExtendEdges_le h₀).1

/-- There are finitely many extend edges of `Ext(c)` from a target `c`. -/
theorem finite_targetExtendEdges [Finite H.verts] (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsProper) : (H.targetExtendEdges s t c).Finite :=
  (h.finite_and_ncard_targetExtendEdges_le h₀).1

/-- At most one extend edge per source: `Ext(c)`, `c` a source, has at most `|s|` extend edges. -/
theorem ncard_sourceExtendEdges_le [Finite H.verts] (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsProper) : (H.sourceExtendEdges s t c).ncard ≤ s.ncard :=
  (h.finite_and_ncard_sourceExtendEdges_le h₀).2

/-- At most one extend edge per target: `Ext(c)`, `c` a target, has at most `|t|` extend edges. -/
theorem ncard_targetExtendEdges_le [Finite H.verts] (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsProper) : (H.targetExtendEdges s t c).ncard ≤ t.ncard :=
  (h.finite_and_ncard_targetExtendEdges_le h₀).2

/-- Baligács 2026, Lemma 17 (proof): `Ext(c) ∪ Ext(c')`, for a source `c` and a target `c'`,
consists of six groups of at most `n = |s| = |t|` edges each: `E_min`, `E_max`, the edges at `c`,
the edges at `c'`, at most one extend edge per source and at most one per target. -/
theorem ncard_extStar_union_le [Finite H.verts] (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsProper) {c c' : V} :
    (H.extStarSource s t c ∪ H.extStarTarget s t c').ncard ≤ 6 * s.ncard := by
  have h₁ := h.ncard_eq h₀
  -- the union of the two stars is the union of the six groups
  have h₂ : H.extStarSource s t c ∪ H.extStarTarget s t c' =
      H.eMin s ∪ H.eMax s ∪ H.incidentEdges c t ∪ H.incidentEdges c' s ∪
        H.sourceExtendEdges s t c ∪ H.targetExtendEdges s t c' := by
    ext e
    simp only [extStarSource, extStarTarget, Set.mem_union]
    tauto
  -- each group has at most `n` edges
  have b₁ := ncard_eMin_le (G := H.toTemporalGraph) h.finite_left
  have b₂ := ncard_eMax_le (G := H.toTemporalGraph) h.finite_left
  have b₃ := ncard_incidentEdges_le (G := H.toTemporalGraph) (x := c) h.finite_right
  have b₄ := ncard_incidentEdges_le (G := H.toTemporalGraph) (x := c') h.finite_left
  have b₅ := h.ncard_sourceExtendEdges_le h₀ (c := c)
  have b₆ := h.ncard_targetExtendEdges_le h₀ (c := c')
  -- the sizes of the five successive unions are bounded by the sum of the sizes of the parts
  have u₁ := Set.ncard_union_le (H.eMin s) (H.eMax s)
  have u₂ := Set.ncard_union_le (H.eMin s ∪ H.eMax s) (H.incidentEdges c t)
  have u₃ := Set.ncard_union_le (H.eMin s ∪ H.eMax s ∪ H.incidentEdges c t)
    (H.incidentEdges c' s)
  have u₄ := Set.ncard_union_le (H.eMin s ∪ H.eMax s ∪ H.incidentEdges c t ∪
    H.incidentEdges c' s) (H.sourceExtendEdges s t c)
  have u₅ := Set.ncard_union_le (H.eMin s ∪ H.eMax s ∪ H.incidentEdges c t ∪
    H.incidentEdges c' s ∪ H.sourceExtendEdges s t c) (H.targetExtendEdges s t c')
  rw [h₂]
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
    (h₇ : ∃ k ∈ H.arcTime c x, ∃ l ∈ H.arcTime c u, k ≤ l) :
    (Subgraph.fromEdgeSet G (H.extStarSource s t c)).Reachable v u' := by
  obtain ⟨k, hk, l, hl, hkl⟩ := h₇
  replace hk := Option.mem_def.1 hk
  replace hl := Option.mem_def.1 hl
  have hx : x ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₂ h₄
  have hz : z ∈ s := h.mem_left_of_latestNeighborFn_eq_some h₃ h₅
  -- `arcTime` is symmetric in a simple graph
  have hcomm : ∀ p q, H.arcTime p q = H.arcTime q p := arcTime_comm h₀
  -- the arc times of the edges `v x`, `u' z` and `u z`, `c z`
  obtain ⟨a, ha, -⟩ := h.exists_earliestEdge_of_earliestNeighborFn_eq_some h₀ h₁ (.inl h₂) h₄
  obtain ⟨m, hm⟩ := h.exists_arcTime_eq_some_right h₀ h₃ hz
  obtain ⟨a', ha', b', hb', hab'⟩ := h₆.2.1
  replace ha' := Option.mem_def.1 ha'
  replace hb' := Option.mem_def.1 hb'
  have hlb : l = a' := Option.some_inj.1 (hl.symm.trans ((hcomm c u).trans ha'))
  -- start at `v`
  have hv : (Subgraph.fromEdgeSet G (H.extStarSource s t c)).ReachableWithin v v 0 0 :=
    .refl v le_rfl
  -- `v → x`, an edge of `E_min`
  have hvx := hv.step_fromEdgeSet (H := H) ha
    (eMin_subset_extStarSource (h.mem_eMin h₀ h₁ (.inl h₂) h₄ ha)) (Nat.zero_le _)
  -- `x → c`, an edge at `c`; temporal since `{v, x}` is the earliest edge at `x`
  have hxc := hvx.step_fromEdgeSet (H := H) ((hcomm x c).trans hk)
    (mem_of_mem_swap (incidentEdges_subset_extStarSource (mem_incidentEdges hx hk)))
    (h.arcTime_le_of_earliestNeighborFn_eq_some h₀ h₁ (.inl h₂) h₄ ha ((hcomm x c).trans hk))
  -- `c → u`, an edge at `c`
  have hcu := hxc.step_fromEdgeSet (H := H) hl
    (incidentEdges_subset_extStarSource (mem_incidentEdges h₆.1 hl)) hkl
  -- `u → z`, the extend edge of `z`; temporal by definition of the extend index (`l = a' < b'`)
  have huz := hcu.step_fromEdgeSet (H := H) hb'
    (mem_of_mem_swap
      (sourceExtendEdges_subset_extStarSource ⟨z, hz, u, h₆, b', (hcomm z u).trans hb', rfl⟩))
    (hlb.trans_le hab'.le)
  -- `z → u'`, an edge of `E_max`; temporal since it is the latest edge at `z`
  have hzu' := huz.step_fromEdgeSet (H := H) ((hcomm z u').trans hm)
    (mem_of_mem_swap (eMax_subset_extStarSource (h.mem_eMax h₀ h₁ (.inr h₃) h₅ hm)))
    (h.arcTime_le_of_latestNeighborFn_eq_some h₀ h₁ (.inr h₃) h₅ hm ((hcomm z u).trans hb'))
  exact hzu'.reachable

/-- Baligács 2026, Lemma 13 (b): in the `c`-ordered labeling of the sources (by decreasing time at
`c`), let `x = N_min(v)` and let `u = sᵢ` be the extend index of `x`. For `z = N_max(u')` with
`z = s_j`, `j ≤ i`, `Ext(c)` reaches `u'` from `v`, through the temporal walk
`(v, x, u, c, z, u')`. -/
theorem reachable_extStarTarget (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple)
    (h₁ : H.IsProper) (h₂ : v ∈ s) (h₃ : u' ∈ t) (h₄ : H.earliestNeighborFn v = some x)
    (h₅ : H.latestNeighborFn u' = some z) (h₆ : H.IsTargetExtendSource s c x u)
    (h₇ : ∃ k ∈ H.arcTime c u, ∃ l ∈ H.arcTime c z, k ≤ l) :
    (Subgraph.fromEdgeSet G (H.extStarTarget s t c)).Reachable v u' := by
  obtain ⟨k, hk, l, hl, hkl⟩ := h₇
  replace hk := Option.mem_def.1 hk
  replace hl := Option.mem_def.1 hl
  have hx : x ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₂ h₄
  have hz : z ∈ s := h.mem_left_of_latestNeighborFn_eq_some h₃ h₅
  -- `arcTime` is symmetric in a simple graph
  have hcomm : ∀ p q, H.arcTime p q = H.arcTime q p := arcTime_comm h₀
  -- the arc times of the edges `v x`, `u' z` and `u x`, `u c`
  obtain ⟨a, ha, -⟩ := h.exists_earliestEdge_of_earliestNeighborFn_eq_some h₀ h₁ (.inl h₂) h₄
  obtain ⟨m, hm⟩ := h.exists_arcTime_eq_some_right h₀ h₃ hz
  obtain ⟨a', ha', b', hb', hab'⟩ := h₆.2.1
  replace ha' := Option.mem_def.1 ha'
  replace hb' := Option.mem_def.1 hb'
  have hkb : k = b' := Option.some_inj.1 (hk.symm.trans ((hcomm c u).trans hb'))
  -- start at `v`
  have hv : (Subgraph.fromEdgeSet G (H.extStarTarget s t c)).ReachableWithin v v 0 0 :=
    .refl v le_rfl
  -- `v → x`, an edge of `E_min`
  have hvx := hv.step_fromEdgeSet (H := H) ha
    (eMin_subset_extStarTarget (h.mem_eMin h₀ h₁ (.inl h₂) h₄ ha)) (Nat.zero_le _)
  -- `x → u`, the extend edge of `x`; temporal since `{v, x}` is the earliest edge at `x`
  have hxu := hvx.step_fromEdgeSet (H := H) ((hcomm x u).trans ha')
    (mem_of_mem_swap (targetExtendEdges_subset_extStarTarget ⟨x, hx, u, h₆, a', ha', rfl⟩))
    (h.arcTime_le_of_earliestNeighborFn_eq_some h₀ h₁ (.inl h₂) h₄ ha ((hcomm x u).trans ha'))
  -- `u → c`, an edge at `c`; temporal by definition of the extend index
  have huc := hxu.step_fromEdgeSet (H := H) hb'
    (mem_of_mem_swap
      (incidentEdges_subset_extStarTarget (mem_incidentEdges h₆.1 ((hcomm c u).trans hb'))))
    hab'.le
  -- `c → z`, an edge at `c`; temporal since `b' = k ≤ l`
  have hcz := huc.step_fromEdgeSet (H := H) hl
    (incidentEdges_subset_extStarTarget (mem_incidentEdges hz hl)) (hkb.symm.trans_le hkl)
  -- `z → u'`, an edge of `E_max`; temporal since it is the latest edge at `z`
  have hzu' := hcz.step_fromEdgeSet (H := H) ((hcomm z u').trans hm)
    (mem_of_mem_swap (eMax_subset_extStarTarget (h.mem_eMax h₀ h₁ (.inr h₃) h₅ hm)))
    (h.arcTime_le_of_latestNeighborFn_eq_some h₀ h₁ (.inr h₃) h₅ hm ((hcomm z c).trans hl))
  exact hzu'.reachable

end Reachability

section NotReachable

variable [Finite H.verts] [H.IsSymm] {x z : V}

/-- Baligács 2026, Lemma 14 (a): if `Ext(c)` does not reach `u'` from `v`, with `x = N_min(v)` and
`z = N_max(u')`, then `pos_x(z) ≤ pos_x(c)`: the edge `{x, z}` comes no later than the edge
`{x, c}`. -/
theorem arcTime_le_of_not_reachable_extStarSource (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) (h₂ : c ∈ s) (h₃ : v ∈ s) (h₄ : u' ∈ t)
    (h₅ : H.earliestNeighborFn v = some x) (h₆ : H.latestNeighborFn u' = some z)
    (h₇ : ¬(Subgraph.fromEdgeSet G (H.extStarSource s t c)).Reachable v u') :
    ∃ k ∈ H.arcTime x z, ∃ l ∈ H.arcTime x c, k ≤ l := by
  by_contra hnot
  have hx : x ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₃ h₅
  have hz : z ∈ s := h.mem_left_of_latestNeighborFn_eq_some h₄ h₆
  obtain ⟨k, hk⟩ := h.exists_arcTime_eq_some_right h₀ hx hz
  obtain ⟨l, hl⟩ := h.exists_arcTime_eq_some_right h₀ hx h₂
  -- the negated conclusion says `{x, c}` comes strictly before `{x, z}`
  have hlk : l < k := lt_of_not_ge fun hkl ↦ hnot ⟨k, hk, l, hl, hkl⟩
  -- the targets `y` with `pos_y(c) < pos_y(z)`: a finite set, containing `x`
  have hxS : x ∈ {y ∈ t | ∃ a ∈ H.arcTime y c, ∃ b ∈ H.arcTime y z, a < b} :=
    ⟨hx, l, hl, k, hk, hlk⟩
  -- its last element `u` in the `c`-ordered labeling is the extend index of `z`
  obtain ⟨u, ⟨hu, hu₁⟩, hu₂⟩ := exists_max_of_isSome (H.arcTime c)
    (h.finite_right.subset (Set.sep_subset _ _)) ⟨x, hxS⟩
    (fun y hy ↦ h.exists_arcTime_eq_some_left h₀ h₂ hy.1)
  -- so Lemma 13 (a) reaches `u'` from `v`, since `x` comes no later than `u`
  exact h₇ (h.reachable_extStarSource h₀ h₁ h₃ h₄ h₅ h₆
    ⟨hu, hu₁, fun y hy hy' ↦ hu₂ y ⟨hy, hy'⟩⟩ (hu₂ x hxS))

/-- Baligács 2026, Lemma 14 (b): if `Ext(c)` does not reach `u'` from `v`, with `c` a target,
`x = N_min(v)` and `z = N_max(u')`, then `pos_z(c) ≤ pos_z(x)`: the edge `{z, c}` comes no later
than the edge `{z, x}`. -/
theorem arcTime_le_of_not_reachable_extStarTarget (h : H.IsExtremallyMatched s t)
    (h₀ : H.IsSimple) (h₁ : H.IsProper) (h₂ : c ∈ t) (h₃ : v ∈ s) (h₄ : u' ∈ t)
    (h₅ : H.earliestNeighborFn v = some x) (h₆ : H.latestNeighborFn u' = some z)
    (h₇ : ¬(Subgraph.fromEdgeSet G (H.extStarTarget s t c)).Reachable v u') :
    ∃ k ∈ H.arcTime z c, ∃ l ∈ H.arcTime z x, k ≤ l := by
  by_contra hnot
  have hx : x ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₃ h₅
  have hz : z ∈ s := h.mem_left_of_latestNeighborFn_eq_some h₄ h₆
  obtain ⟨k, hk⟩ := h.exists_arcTime_eq_some_left h₀ hz h₂
  obtain ⟨l, hl⟩ := h.exists_arcTime_eq_some_left h₀ hz hx
  -- the negated conclusion says `{z, x}` comes strictly before `{z, c}`
  have hlk : l < k := lt_of_not_ge fun hkl ↦ hnot ⟨k, hk, l, hl, hkl⟩
  -- the sources `y` with `pos_y(x) < pos_y(c)`: a finite set, containing `z`
  have hzS : z ∈ {y ∈ s | ∃ a ∈ H.arcTime y x, ∃ b ∈ H.arcTime y c, a < b} :=
    ⟨hz, l, hl, k, hk, hlk⟩
  -- its last element `u` in the `c`-ordered labeling is the extend index of `x`
  obtain ⟨u, ⟨hu, hu₁⟩, hu₂⟩ := exists_min_of_isSome (H.arcTime c)
    (h.finite_left.subset (Set.sep_subset _ _)) ⟨z, hzS⟩
    (fun y hy ↦ h.exists_arcTime_eq_some_right h₀ h₂ hy.1)
  -- so Lemma 13 (b) reaches `u'` from `v`, since `z` comes no later than `u`
  exact h₇ (h.reachable_extStarTarget h₀ h₁ h₃ h₄ h₅ h₆
    ⟨hu, hu₁, fun y hy hy' ↦ hu₂ y ⟨hy, hy'⟩⟩ (hu₂ z hzS))

/-- Baligács 2026, Corollary 15: if `Ext(c) ∪ Ext(d)`, for a source `c` and a target `d`, does not
reach `u'` from `v`, with `x = N_min(v)` and `z = N_max(u')`, then the walk `(d, z, x, c)` is
temporal, that is `pos_z(d) ≤ pos_z(x)` and `pos_x(z) ≤ pos_x(c)`. (Its first junction, at `d`, is
the one of the walk `(N_min(d), d, z, x, c)`, temporal for free since `N_min(d)` is the earliest
neighbor of `d`.) -/
theorem arcTime_chain_of_not_reachable (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple)
    (h₁ : H.IsProper) {d : V} (h₂ : c ∈ s) (h₃ : d ∈ t) (h₄ : v ∈ s) (h₅ : u' ∈ t)
    (h₆ : H.earliestNeighborFn v = some x) (h₇ : H.latestNeighborFn u' = some z)
    (h₈ : ¬(Subgraph.fromEdgeSet G (H.extStarSource s t c ∪ H.extStarTarget s t d)).Reachable
      v u') :
    (∃ a ∈ H.arcTime d z, ∃ b ∈ H.arcTime z x, a ≤ b) ∧
      ∃ a ∈ H.arcTime z x, ∃ b ∈ H.arcTime x c, a ≤ b := by
  -- neither extended star reaches `u'` from `v`
  have hjunction_x := h.arcTime_le_of_not_reachable_extStarSource h₀ h₁ h₂ h₄ h₅ h₆ h₇ fun hr ↦
    h₈ (Reachable.mono (Subgraph.toTemporalGraph_le
      (Subgraph.fromEdgeSet_mono Set.subset_union_left)) hr)
  have hjunction_z := h.arcTime_le_of_not_reachable_extStarTarget h₀ h₁ h₃ h₄ h₅ h₆ h₇ fun hr ↦
    h₈ (Reachable.mono (Subgraph.toTemporalGraph_le
      (Subgraph.fromEdgeSet_mono Set.subset_union_right)) hr)
  -- the junction at `x` is Lemma 14 (a), the one at `z` is Lemma 14 (b)
  rw [arcTime_comm h₀ x z] at hjunction_x
  rw [arcTime_comm h₀ z d] at hjunction_z
  exact ⟨hjunction_z, hjunction_x⟩

/-- Baligács 2026, Lemma 16: in the `c`-ordered labeling cut at `k` (threshold `τ`), every upper
source `v = sᵢ` (`i > k`) either is 3-hop-`k`-cut-crossing, or `Ext(c) ∪ Ext(w)` reaches every
target from every early source `s_j` (`j ≤ k`). Here `w = tᵢ = N_min(v)`. If the reachability fails
at some `(s_j, y)`, Corollary 15 makes `(v, w, z, p, c)` a temporal walk, with `p = N_min(s_j)` and
`z = N_max(y)`, which is a 3-hop crossing. -/
theorem isCutCrossing_or_reachable (h : H.IsExtremallyMatched s t) (h₀ : H.IsSimple)
    (h₁ : H.IsProper) (h₂ : c ∈ s) (τ : ℕ) {w : V} (h₃ : v ∈ s)
    (h₄ : H.earliestNeighborFn v = some w) (h₅ : ∃ k ∈ H.arcTime c w, τ < k) :
    H.IsCutCrossing s c τ 3 v ∨
      ∀ x ∈ {x ∈ s | ∃ u ∈ H.earliestNeighborFn x, ∃ k ∈ H.arcTime c u, k ≤ τ}, ∀ y ∈ t,
        (Subgraph.fromEdgeSet G (H.extStarSource s t c ∪ H.extStarTarget s t w)).Reachable x y := by
  refine or_iff_not_imp_right.2 fun h₆ ↦ ?_
  -- some pair `(s_j, y)` with `j ≤ k` is not reached
  push Not at h₆
  obtain ⟨x, ⟨hx, p, hp, hxτ⟩, y, hy, h₇⟩ := h₆
  have hw : w ∈ t := h.mem_right_of_earliestNeighborFn_eq_some h₃ h₄
  obtain ⟨z, hz⟩ := h.exists_latestNeighborFn_eq_some (.inr hy)
  -- Corollary 15 with `d = N_min(v)`
  obtain ⟨⟨a₁, ha₁, b₁, hb₁, hdz⟩, ⟨a₂, ha₂, b₂, hb₂, hzx⟩⟩ :=
    h.arcTime_chain_of_not_reachable h₀ h₁ h₂ hw hx hy (Option.mem_def.1 hp) hz h₇
  obtain ⟨n, hn, -⟩ := h.exists_earliestEdge_of_earliestNeighborFn_eq_some h₀ h₁ (.inl h₃) h₄
  replace ha₁ := Option.mem_def.1 ha₁
  replace hb₁ := Option.mem_def.1 hb₁
  -- the junction at `w` is temporal, since `{v, w}` is the earliest edge at `w`
  have hvw : n ≤ a₁ := h.arcTime_le_of_earliestNeighborFn_eq_some h₀ h₁ (.inl h₃) h₄ hn ha₁
  -- the 3-hop walk `(v, w, z, p)`, whose last edge `{z, p}` is at time `b₁`
  let hwalk := ((NonemptyTemporalWalk.single (adj_of_arcTime_eq_some hn)).step
    (adj_of_arcTime_eq_some ha₁) hvw).step (adj_of_arcTime_eq_some hb₁) hdz
  -- it ends no later than the edge `{p, c}`
  refine ⟨⟨w, Option.mem_def.2 h₄, h₅⟩, x, hx, p, hp, hxτ, n, b₁, .ofNonempty hwalk, le_rfl,
    b₂, hb₂, ?_⟩
  -- the arc `z p` has one time
  obtain rfl : a₂ = b₁ := Option.mem_unique ha₂ hb₁
  exact hzx

end NotReachable

end IsExtremallyMatched

end TemporalGraph
