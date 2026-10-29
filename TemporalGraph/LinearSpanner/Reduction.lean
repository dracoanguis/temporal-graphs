/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.LinearSpanner.ExtremallyMatched
public import TemporalGraph.Dismountability.OneSidedBound

/-!
# Reduction to extremally matched bi-cliques

Baligács 2026, §2.3. A temporal bi-clique without dismountable vertex is extremally matched, and
the dismountable vertices of any bi-clique can be deleted one by one, at two edges each, until
none is left: a one-sided spanner of the remaining extremally matched bi-clique extends to one of
the whole bi-clique.

## Main results

* `TemporalGraph.Subgraph.isExtremallyMatched_of_not_dismountable` : a finite simple bi-clique on
  two nonempty parts, without dismountable source nor target, is extremally matched.
* `TemporalGraph.Subgraph.exists_isExtremallyMatched_reduction` : Baligács 2026, Lemma 5
  (Dismountability): every finite simple bi-clique contains an extremally matched bi-clique on
  parts `s' ⊆ s`, `t' ⊆ t`, of which every symmetric one-sided spanner extends to one of the whole
  bi-clique with at most two more edges per deleted vertex.

## References

* Júlia Baligács, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156v1 (2026), §2.3.
-/

@[expose] public section

universe u

namespace TemporalGraph

namespace Subgraph

variable {V : Type u} {G : TemporalGraph V}

/-- Without dismountable source, if `w` is the earliest neighbor of a source `v`, then `v` is the
only earliest neighbor of `w`. -/
private theorem earliestEdge_reciprocal_of_not_sourceDismountable {H : Subgraph G} [H.IsSymm]
    {s t : Set V} (h₀ : H.IsBicliqueWith s t) (h₁ : ∀ x, ¬H.SourceDismountable s t x)
    {v w u : V} {n m : ℕ} (h₂ : v ∈ s) (h₃ : H.EarliestEdge v w n) (h₄ : H.EarliestEdge w u m) :
    u = v := by
  by_contra hne
  have hw : w ∈ t := h₀.isBipartiteWith.mem_of_mem_adj h₂ h₃.1
  -- `u` hides behind `v` through `w`, the edge `w u` being no later than `w v`
  exact h₁ u ⟨h₀.isBipartiteWith.mem_of_mem_adj' hw h₄.1, v, h₂, Ne.symm hne, w, hw, n, m, h₃,
    h₄.1, h₄.2 v n h₃.1.symm⟩

/-- Without dismountable target, if `w` is the latest neighbor of a target `v`, then `v` is the
only latest neighbor of `w`. -/
private theorem latestEdge_reciprocal_of_not_oneSidedDismountable {H : Subgraph G} [H.IsSymm]
    {s t : Set V} (h₀ : H.IsBicliqueWith s t) (h₁ : ∀ x, ¬H.OneSidedDismountable s t x)
    {v w u : V} {n m : ℕ} (h₂ : v ∈ t) (h₃ : H.LatestEdge v w n) (h₄ : H.LatestEdge w u m) :
    u = v := by
  by_contra hne
  have hw : w ∈ s := h₀.isBipartiteWith.mem_of_mem_adj' h₂ h₃.1
  exact h₁ u ⟨h₀.isBipartiteWith.mem_of_mem_adj hw h₄.1, v, h₂, Ne.symm hne, w, hw, n, m, h₃,
    h₄.1, h₄.2 v n h₃.1.symm⟩

/-- Without dismountable source, `N_min` sends a source `v` to a target `w`, and the earliest edge
at `w` is the same edge. -/
private theorem exists_earliestEdge_pair_of_not_sourceDismountable {H : Subgraph G} [Finite H.verts]
    [H.IsSymm] {s t : Set V} (h₀ : H.IsSimple) (h₁ : H.IsBicliqueWith s t)
    (h₂ : s.Nonempty) (h₃ : t.Nonempty)
    (h₄ : ∀ x, ¬H.SourceDismountable s t x) {v : V} (h₅ : v ∈ s) :
    ∃ w ∈ t, H.earliestNeighborFn v = some w ∧
      ∃ n, H.EarliestEdge v w n ∧ H.EarliestEdge w v n := by
  obtain ⟨y, -, n₀, hy⟩ := exists_earliestEdge_of_isBicliqueWith h₀ h₁.symm h₃ h₅
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (earliestNeighborFn_isSome_iff.2 ⟨y, n₀, hy⟩)
  obtain ⟨n, hvw⟩ := earliestNeighbor_of_earliestNeighborFn_eq_some hw
  have hwt : w ∈ t := h₁.isBipartiteWith.mem_of_mem_adj h₅ hvw.1
  -- the earliest edge at `w` goes to `v`, with the same time (the graph is simple)
  obtain ⟨u, -, m, hwu⟩ := exists_earliestEdge_of_isBicliqueWith h₀ h₁ h₂ hwt
  obtain rfl := earliestEdge_reciprocal_of_not_sourceDismountable h₁ h₄ h₅ hvw hwu
  obtain rfl : m = n := h₀ hwu.1 hvw.1.symm
  exact ⟨w, hwt, hw, m, hvw, hwu⟩

/-- Without dismountable target, `N_max` sends a target `v` to a source `w`, and the latest edge
at `w` is the same edge. -/
private theorem exists_latestEdge_pair_of_not_oneSidedDismountable {H : Subgraph G} [Finite H.verts]
    [H.IsSymm] {s t : Set V} (h₀ : H.IsSimple) (h₁ : H.IsBicliqueWith s t)
    (h₂ : s.Nonempty) (h₃ : t.Nonempty)
    (h₄ : ∀ x, ¬H.OneSidedDismountable s t x) {v : V} (h₅ : v ∈ t) :
    ∃ w ∈ s, H.latestNeighborFn v = some w ∧
      ∃ n, H.LatestEdge v w n ∧ H.LatestEdge w v n := by
  obtain ⟨y, -, n₀, hy⟩ := exists_latestEdge_of_isBicliqueWith h₀ h₁ h₂ h₅
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (latestNeighborFn_isSome_iff.2 ⟨y, n₀, hy⟩)
  obtain ⟨n, hvw⟩ := latestNeighbor_of_latestNeighborFn_eq_some hw
  have hws : w ∈ s := h₁.isBipartiteWith.mem_of_mem_adj' h₅ hvw.1
  obtain ⟨u, -, m, hwu⟩ := exists_latestEdge_of_isBicliqueWith h₀ h₁.symm h₃ hws
  obtain rfl := latestEdge_reciprocal_of_not_oneSidedDismountable h₁ h₄ h₅ hvw hwu
  obtain rfl : m = n := h₀ hwu.1 hvw.1.symm
  exact ⟨w, hws, hw, m, hvw, hwu⟩

/-- Baligács 2026, §2.3: a finite simple bi-clique on nonempty parts `s` and `t`, with neither a
dismountable source nor a dismountable target, is extremally matched. Without dismountable source,
`N_min` injects `s` into `t` (the earliest neighbor of `N_min v` is `v`), so `|s| ≤ |t|`; without
dismountable target, `N_max` injects `t` into `s`. Hence `N_min : s → t` and `N_max : t → s` are
bijections, and every vertex of `s ∪ t` has the earliest (resp. latest) edge of its partner. -/
theorem isExtremallyMatched_of_not_dismountable {H : Subgraph G} [Finite H.verts] [H.IsSymm]
    {s t : Set V} (h₀ : H.IsSimple) (h₁ : H.IsBicliqueWith s t) (h₂ : s.Nonempty)
    (h₃ : t.Nonempty) (h₄ : ∀ x, ¬H.SourceDismountable s t x)
    (h₅ : ∀ x, ¬H.OneSidedDismountable s t x) : H.IsExtremallyMatched s t := by
  have hsub : s ∪ t ⊆ H.verts := isBicliqueWith_subset_verts h₁ h₂ h₃
  have hsfin : s.Finite := (Set.toFinite H.verts).subset (Set.subset_union_left.trans hsub)
  have htfin : t.Finite := (Set.toFinite H.verts).subset (Set.subset_union_right.trans hsub)
  have hmin := fun v (hv : v ∈ s) ↦
    exists_earliestEdge_pair_of_not_sourceDismountable h₀ h₁ h₂ h₃ h₄ hv
  have hmax := fun v (hv : v ∈ t) ↦
    exists_latestEdge_pair_of_not_oneSidedDismountable h₀ h₁ h₂ h₃ h₅ hv
  -- `N_min` is injective on `s`: two sources with the same `N_min` are both the earliest
  -- neighbor of it
  have injOn_min : s.InjOn H.earliestNeighborFn := by
    intro a ha b hb hab
    obtain ⟨w, -, hw, n, han, -⟩ := hmin a ha
    obtain ⟨w', -, hw', m, -, hwb⟩ := hmin b hb
    obtain rfl : w' = w := Option.some_injective _ (hw'.symm.trans (hab ▸ hw))
    exact (earliestEdge_reciprocal_of_not_sourceDismountable h₁ h₄ ha han hwb).symm
  -- likewise `N_max` is injective on `t`
  have injOn_max : t.InjOn H.latestNeighborFn := by
    intro a ha b hb hab
    obtain ⟨w, -, hw, n, han, -⟩ := hmax a ha
    obtain ⟨w', -, hw', m, -, hwb⟩ := hmax b hb
    obtain rfl : w' = w := Option.some_injective _ (hw'.symm.trans (hab ▸ hw))
    exact (latestEdge_reciprocal_of_not_oneSidedDismountable h₁ h₅ ha han hwb).symm
  have mapsTo_min : Set.MapsTo H.earliestNeighborFn s (some '' t) := fun v hv ↦
    let ⟨w, hw, h, _⟩ := hmin v hv
    ⟨w, hw, h.symm⟩
  have mapsTo_max : Set.MapsTo H.latestNeighborFn t (some '' s) := fun v hv ↦
    let ⟨w, hw, h, _⟩ := hmax v hv
    ⟨w, hw, h.symm⟩
  -- hence `|s| = |t|`
  have hst : s.ncard ≤ t.ncard := by
    rw [← Set.ncard_image_of_injective t (Option.some_injective V)]
    exact Set.ncard_le_ncard_of_injOn _ mapsTo_min injOn_min (htfin.image _)
  have hts : t.ncard ≤ s.ncard := by
    rw [← Set.ncard_image_of_injective s (Option.some_injective V)]
    exact Set.ncard_le_ncard_of_injOn _ mapsTo_max injOn_max (hsfin.image _)
  -- so `N_min` maps `s` onto `t`, and `N_max` maps `t` onto `s`
  have image_min : H.earliestNeighborFn '' s = some '' t :=
    Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.2 mapsTo_min)
      (by rw [injOn_min.ncard_image, Set.ncard_image_of_injective _ (Option.some_injective V)]
          exact hts)
      (htfin.image _)
  have image_max : H.latestNeighborFn '' t = some '' s :=
    Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.2 mapsTo_max)
      (by rw [injOn_max.ncard_image, Set.ncard_image_of_injective _ (Option.some_injective V)]
          exact hst)
      (hsfin.image _)
  refine ⟨h₁, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · rcases hv with hv | hv
    · obtain ⟨w, -, -, n, hvw, hwv⟩ := hmin v hv
      exact ⟨w, n, hvw, hwv⟩
    · -- the target `v` is `N_min u` for a source `u`, and `u` is its earliest neighbor
      obtain ⟨u, hu, hu'⟩ := image_min ▸ Set.mem_image_of_mem some hv
      obtain ⟨w, -, hw, n, huw, hwu⟩ := hmin u hu
      obtain rfl : w = v := Option.some_injective _ (hw.symm.trans hu')
      exact ⟨u, n, hwu, huw⟩
  · rcases hv with hv | hv
    · -- the source `v` is `N_max u` for a target `u`, and `u` is its latest neighbor
      obtain ⟨u, hu, hu'⟩ := image_max ▸ Set.mem_image_of_mem some hv
      obtain ⟨w, -, hw, n, huw, hwu⟩ := hmax u hu
      obtain rfl : w = v := Option.some_injective _ (hw.symm.trans hu')
      exact ⟨u, n, hwu, huw⟩
    · obtain ⟨w, -, -, n, hvw, hwv⟩ := hmax v hv
      exact ⟨w, n, hvw, hwv⟩

/-- Baligács 2026, Lemma 5 (Dismountability): every finite simple bi-clique `H` on `s`, `t`
contains an extremally matched bi-clique `H.induce (s' ∪ t')`, with `s' ⊆ s` and `t' ⊆ t`, such
that every symmetric one-sided spanner of it extends to a symmetric one-sided spanner of `H` with
at most `2 (|s| + |t| - |s'| - |t'|)` more edges (two per deleted vertex). The bound is stated
additively, to avoid truncated subtraction. -/
theorem exists_isExtremallyMatched_reduction {H : Subgraph G} [Finite H.verts] [G.IsSymm]
    [H.IsSymm] {s t : Set V} (h₀ : H.IsSimple) (h₁ : H.IsBicliqueWith s t) :
    ∃ s' ⊆ s, ∃ t' ⊆ t, s' ∪ t' ⊆ H.verts ∧
      (H.induce (s' ∪ t')).IsExtremallyMatched s' t' ∧
      ∀ K : Subgraph G, K.IsSymm → K.IsSpannerFromTo (H.induce (s' ∪ t')) s' t' →
        ∃ K' : Subgraph G, K'.IsSymm ∧ K'.IsSpannerFromTo H s t ∧
          K'.edgeSet.ncard + 2 * (s'.ncard + t'.ncard) ≤
            K.edgeSet.ncard + 2 * (s.ncard + t.ncard) := by
  induction hk : s.ncard + t.ncard using Nat.strong_induction_on generalizing H s t with
  | _ k ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · -- no source: nothing to reduce, `K` itself is a (vacuous) spanner
      have hempty : (∅ : Set V) ∪ ∅ ⊆ H.verts := by simp only [Set.union_self, Set.empty_subset]
      refine ⟨∅, subset_rfl, ∅, Set.empty_subset _, hempty, ?_, fun K hK hspan ↦ ?_⟩
      · rw [Set.union_empty]
        exact isExtremallyMatched_induce_empty
      · refine ⟨K, hK, ⟨hspan.1.trans (induce_le_of_subset hempty), fun x hx ↦ hx.elim⟩, ?_⟩
        -- the empty parts add no edge: `|K.edgeSet| + 2 (0 + 0) ≤ |K.edgeSet| + 2 (0 + |t|)`
        simp only [Set.ncard_empty]
        omega
    rcases t.eq_empty_or_nonempty with rfl | ht
    · -- no target: likewise
      have hempty : (∅ : Set V) ∪ ∅ ⊆ H.verts := by simp only [Set.union_self, Set.empty_subset]
      refine ⟨∅, Set.empty_subset _, ∅, subset_rfl, hempty, ?_, fun K hK hspan ↦ ?_⟩
      · rw [Set.union_empty]
        exact isExtremallyMatched_induce_empty
      · refine ⟨K, hK, ⟨hspan.1.trans (induce_le_of_subset hempty), fun _ _ y hy ↦ hy.elim⟩, ?_⟩
        simp only [Set.ncard_empty]
        omega
    have hsub : s ∪ t ⊆ H.verts := isBicliqueWith_subset_verts h₁ hs ht
    have hspos : 0 < s.ncard :=
      hs.ncard_pos ((Set.toFinite H.verts).subset (Set.subset_union_left.trans hsub))
    have htpos : 0 < t.ncard :=
      ht.ncard_pos ((Set.toFinite H.verts).subset (Set.subset_union_right.trans hsub))
    by_cases hsrc : ∃ x, H.SourceDismountable s t x
    · -- a dismountable source `x`: reduce `H` without `x`, then put `x` back at two edges
      obtain ⟨x, hdis⟩ := hsrc
      obtain ⟨-, hbc, hcard⟩ := deleteVerts_subproblem_source h₀ h₁ hdis.1
        (Set.disjoint_left.mp h₁.isBipartiteWith.disjoint hdis.1)
      -- `|s \ {x}| = |s| - 1` with `|s| > 0`, so the measure `|s| + |t|` decreases
      obtain ⟨s', hs', t', ht', hverts, hem, hext⟩ :=
        ih ((s \ {x}).ncard + t.ncard) (by omega) (h₀.mono (toTemporalGraph_le deleteVerts_le)) hbc
          rfl
      -- `s' ∪ t'` avoids `x`, so inducing on it does not see the deletion
      rw [deleteVerts_induce_of_subset hverts] at hem hext
      refine ⟨s', hs'.trans Set.sdiff_subset, t', ht', hverts.trans Set.sdiff_subset, hem,
        fun K hK hspan ↦ ?_⟩
      obtain ⟨K₁, hK₁, hK₁span, hK₁card⟩ := hext K hK hspan
      obtain ⟨K', hK', hK'span, hK'card⟩ := isSpannerFromTo_of_sourceDismount h₁ hdis hK₁span
      -- `|K'| ≤ |K₁| + 2` and `|K₁| + 2 (|s'| + |t'|) ≤ |K| + 2 (|s| - 1 + |t|)`
      exact ⟨K', hK', hK'span, by omega⟩
    by_cases htgt : ∃ x, H.OneSidedDismountable s t x
    · -- a dismountable target `x`: the mirror image, with the one-sided dismount step
      obtain ⟨x, hdis⟩ := htgt
      obtain ⟨-, hbc, hcard⟩ := deleteVerts_subproblem_target h₀ h₁ hdis.1
        (Set.disjoint_right.mp h₁.isBipartiteWith.disjoint hdis.1)
      -- `|t \ {x}| = |t| - 1` with `|t| > 0`, so the measure decreases
      obtain ⟨s', hs', t', ht', hverts, hem, hext⟩ :=
        ih (s.ncard + (t \ {x}).ncard) (by omega) (h₀.mono (toTemporalGraph_le deleteVerts_le)) hbc
          rfl
      rw [deleteVerts_induce_of_subset hverts] at hem hext
      refine ⟨s', hs', t', ht'.trans Set.sdiff_subset, hverts.trans Set.sdiff_subset, hem,
        fun K hK hspan ↦ ?_⟩
      obtain ⟨K₁, hK₁, hK₁span, hK₁card⟩ := hext K hK hspan
      obtain ⟨K', hK', hK'span, hK'card⟩ := isSpannerFromTo_of_targetDismount h₁ hdis hK₁span
      -- `|K'| ≤ |K₁| + 2` and `|K₁| + 2 (|s'| + |t'|) ≤ |K| + 2 (|s| + |t| - 1)`
      exact ⟨K', hK', hK'span, by omega⟩
    · -- no dismountable vertex: `H` is extremally matched, nothing is deleted
      push Not at hsrc htgt
      have hem := isExtremallyMatched_of_not_dismountable h₀ h₁ hs ht hsrc htgt
      refine ⟨s, subset_rfl, t, subset_rfl, hsub, hem.induce, fun K hK hspan ↦ ?_⟩
      -- a spanner of the induced bi-clique is one of `H`: all sources reach all targets there
      have hbc := isBicliqueWith_induce h₁ (subset_refl s) (subset_refl t)
      exact ⟨K, hK, hspan.of_le (induce_le_of_subset hsub) fun x hx y hy ↦
      reachable_of_isBicliqueWith hbc hx hy, by rw [hk]⟩

end Subgraph

end TemporalGraph
