/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import TemporalGraph.Dismountability.Operations
public import TemporalGraph.LinearSpanner.Bound

/-!
# Linear spanners of temporal cliques

Baligács 2026, §5. This module concludes the proof that a temporal clique on `n` vertices has a
spanner with at most `7 n` edges, by the dismountability technique of SAND 2025.

* A clique that is not `{1,2}`-hop dismountable splits into `V⁻` and `V⁺` (SAND 2025, §3), and
  the bipartite subgraph between them is a bi-clique (SAND 2025, Corollary 4.1) whose earliest
  and latest edges are reciprocal (SAND 2025, Lemma 3.5): it is extremally matched
  (Baligács 2026, Theorem 20).
* Baligács 2026, Theorem 18 spans this bi-clique with at most `14 |V⁺| = 7 n` edges, temporally
  connected.
* The generic dismountability induction (SAND 2025, Theorem 2.1 and §2.1, with 4 more edges per
  dismounted vertex, absorbed by the slope 7) then gives Theorem 2 for any clique.

## Main results

* `TemporalGraph.Subgraph.isExtremallyMatched_between_of_not_twoHopDismountable` : Baligács 2026,
  Theorem 20, as SAND 2025, Corollary 4.1 with Lemma 3.5.
* `TemporalGraph.Subgraph.exists_isSpannerOf_ncard_le_seven_mul_of_not_twoHopDismountable` : the
  non-dismountable case of the induction, with at most `7 n` edges.
* `TemporalGraph.Subgraph.exists_isSpannerOf_ncard_le_seven_mul` : Baligács 2026, Theorem 2.
* `TemporalGraph.Subgraph.exists_isBigO_isSpannerOf_linear` : the `O(n)` form of Theorem 2.

## References

* Júlia Baligács, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156v1 (2026), §5.
* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025
  (LIPIcs 330, doi:10.4230/LIPIcs.SAND.2025.6), §§2–4.
-/

@[expose] public section

universe u

namespace TemporalGraph

namespace Subgraph

variable {V : Type u} {G : TemporalGraph V}

section ExtremallyMatched

/-- Baligács 2026, Theorem 20 (SAND 2025, Corollary 4.1 with Lemma 3.5): in a finite simple
proper clique `H` that is not `{1,2}`-hop dismountable, the bi-clique `H.between V⁻ V⁺` between
`V⁻` and `V⁺` is extremally matched. The sources are `V⁺` and the targets `V⁻`: in Baligács's
notation, the vertices matched by `E_min` to the targets are the sources, and the earliest
(resp. latest) edge of a vertex of `V⁻` (resp. `V⁺`) comes from `V⁺` (resp. `V⁻`)
(SAND 2025, Corollary 3.3), and is also the earliest (resp. latest) edge of its other endpoint,
by reciprocity (SAND 2025, Lemma 3.5). -/
theorem isExtremallyMatched_between_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) (h₃ : ¬H.TwoHopDismountable) :
    (H.between H.vminus H.vplus).IsExtremallyMatched H.vplus H.vminus := by
  have hbc := biclique_of_not_twoHopDismountable h₁ h₃
  have hdisj : Disjoint H.vminus H.vplus := hbc.isBipartiteWith.disjoint
  -- an earliest edge `a b` of `a ∈ V⁺` to `b ∈ V⁻` is the earliest edge at both ends
  have key : ∀ a ∈ H.vplus, ∀ b ∈ H.vminus, ∀ n, H.EarliestEdge a b n →
      (H.between H.vminus H.vplus).EarliestEdge a b n ∧
      (H.between H.vminus H.vplus).EarliestEdge b a n := by
    intro a ha b hb n h
    have hab : (H.between H.vminus H.vplus).Adj a b n := ⟨h.1, Or.inr ⟨ha, hb⟩⟩
    refine ⟨earliestEdge_of_ge between_le h hab, ⟨hab.symm, fun z m hz ↦ ?_⟩⟩
    -- the edges of `b ∈ V⁻` in the bi-clique go to `V⁺`, where reciprocity bounds the time
    have hzp : z ∈ H.vplus := by
      rcases hz.2 with ⟨-, hz⟩ | ⟨hb', -⟩
      · exact hz
      · exact absurd hb' (Set.disjoint_left.mp hdisj hb)
    exact earliestEdge_reciprocity h₁ h₃ h z hzp m hz.1
  -- a latest edge `a b` of `a ∈ V⁻` to `b ∈ V⁺` is the latest edge at both ends
  have key' : ∀ a ∈ H.vminus, ∀ b ∈ H.vplus, ∀ n, H.LatestEdge a b n →
      (H.between H.vminus H.vplus).LatestEdge a b n ∧
      (H.between H.vminus H.vplus).LatestEdge b a n := by
    intro a ha b hb n h
    have hab : (H.between H.vminus H.vplus).Adj a b n := ⟨h.1, Or.inl ⟨ha, hb⟩⟩
    refine ⟨latestEdge_of_ge between_le h hab, ⟨hab.symm, fun z m hz ↦ ?_⟩⟩
    -- the edges of `b ∈ V⁺` in the bi-clique go to `V⁻`, where reciprocity bounds the time
    have hzm : z ∈ H.vminus := by
      rcases hz.2 with ⟨hb', -⟩ | ⟨-, hz⟩
      · exact absurd hb' (Set.disjoint_right.mp hdisj hb)
      · exact hz
    exact latestEdge_reciprocity h₁ h₃ h z hzm m hz.1
  refine ⟨hbc.symm, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · rcases hv with hv | hv
    · -- `v ∈ V⁺`: its earliest edge goes to `V⁻`
      obtain ⟨b, n, h⟩ := earliestEdge_exists_of_finite_nontrivial_simple_clique h₀ h₁ v
        (vplus_sub_verts hv)
      have hb := earliestNeighbor_mem_vminus ⟨n, h⟩
      exact ⟨b, n, (key v hv b hb n h).1, (key v hv b hb n h).2⟩
    · -- `v ∈ V⁻`: SAND 2025, Corollary 3.3, a unique earliest edge from `V⁺`
      obtain ⟨⟨a, n⟩, ⟨ha, h⟩, -⟩ := existsUnique_vplus_earliestEdge h₀ h₁ h₂ h₃ v hv
      exact ⟨a, n, (key a ha v hv n h).2, (key a ha v hv n h).1⟩
  · rcases hv with hv | hv
    · -- `v ∈ V⁺`: SAND 2025, Corollary 3.3, a unique latest edge from `V⁻`
      obtain ⟨⟨a, n⟩, ⟨ha, h⟩, -⟩ := existsUnique_vminus_latestEdge h₀ h₁ h₂ h₃ v hv
      exact ⟨a, n, (key' a ha v hv n h).2, (key' a ha v hv n h).1⟩
    · -- `v ∈ V⁻`: its latest edge goes to `V⁺`
      obtain ⟨b, n, h⟩ := latestEdge_exists_of_finite_nontrivial_simple_clique h₀ h₁ v
        (vminus_sub_verts hv)
      have hb := latestNeighbor_mem_vplus ⟨n, h⟩
      exact ⟨b, n, (key' v hv b hb n h).1, (key' v hv b hb n h).2⟩

end ExtremallyMatched

section Bound

/-- Baligács 2026, §5 (non-dismountable case of Theorem 2): a finite simple proper clique `H`
that is not `{1,2}`-hop dismountable has a symmetric spanner with at most `7 n` edges, where
`n = |H.verts|`. By Theorem 20, `H.between V⁻ V⁺` is extremally matched, and Theorem 18 gives a
spanner of it, temporally connected on `V⁺ ∪ V⁻ = H.verts` (SAND 2025, Lemma 3.4), with at most
`14 |V⁺| = 7 n` edges (SAND 2025, Corollary 3.3 (3)). -/
theorem exists_isSpannerOf_ncard_le_seven_mul_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [G.IsSymm] [G.IsLoopless] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) (h₃ : ¬H.TwoHopDismountable) :
    ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerOf H ∧ K.edgeSet.ncard ≤ 7 * H.verts.ncard := by
  have hem := isExtremallyMatched_between_of_not_twoHopDismountable h₀ h₁ h₂ h₃
  have hBle : H.between H.vminus H.vplus ≤ H := between_le
  have : Finite (H.between H.vminus H.vplus).verts := inferInstanceAs (Finite H.verts)
  -- Theorem 18 on the bi-clique, with sources `V⁺`
  obtain ⟨K, hKsymm, hKspan, hKtc, hKcard⟩ := hem.exists_isSpannerFromTo
    (h₀.mono (toTemporalGraph_le hBle)) (h₂.mono (toTemporalGraph_le hBle))
  -- `V⁰ = ∅`, so `H.verts = V⁺ ∪ V⁻`, of size `2 |V⁺|`
  have hverts : H.verts = H.vplus ∪ H.vminus := by
    rw [Set.union_comm, ← vunion_eq_univ, vzero_empty_of_not_twoHopDismountable h₀ h₁ h₂ h₃,
      Set.union_empty]
  have hdisj := (biclique_of_not_twoHopDismountable h₁ h₃).isBipartiteWith.disjoint
  have hcard := vminus_card_eq_vplus_card h₀ h₁ h₃
  have hn : H.verts.ncard = 2 * H.vplus.ncard := by
    rw [hverts, Set.ncard_union_eq hdisj.symm
      ((Set.toFinite H.verts).subset vplus_sub_verts)
      ((Set.toFinite H.verts).subset vminus_sub_verts)]
    omega
  refine ⟨K, hKsymm, isSpannerOf_of_le_of_temporallyConnected (hKspan.1.trans hBle) ?_, ?_⟩
  · rwa [hverts]
  · omega

/-- Baligács 2026, Theorem 2: every finite simple proper temporal clique on `n` vertices admits
a symmetric spanner with at most `7 n` edges. This is SAND 2025, Theorem 2.1 and §2.1 (the
generic induction `exists_isSpannerOf_ncard_le_of_not_twoHopDismountable`, each dismounted vertex
costing 4 edges, at most the slope 7), with the non-dismountable case Theorem 18 (see
`exists_isSpannerOf_ncard_le_seven_mul_of_not_twoHopDismountable`). -/
theorem exists_isSpannerOf_ncard_le_seven_mul {H : Subgraph G} [Finite H.verts]
    [G.IsSymm] [G.IsLoopless] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerOf H ∧ K.edgeSet.ncard ≤ 7 * H.verts.ncard :=
  exists_isSpannerOf_ncard_le_of_not_twoHopDismountable (fun n ↦ 7 * n) (fun n ↦ by omega)
    (fun h₀ h₁ h₂ h₃ ↦ exists_isSpannerOf_ncard_le_seven_mul_of_not_twoHopDismountable
      h₀ h₁ h₂ h₃) h₀ h₁ h₂

open Asymptotics Filter in
/-- Baligács 2026, Theorem 2, in the form of `exists_isBigO_isSpannerOf`: temporal cliques admit
spanners of size `O(n)`. Precisely, there is `f = O(n)` (namely `f n = 7 n`) such that every
finite, simple, proper clique subgraph `H` (symmetric, in a symmetric loopless ambient graph `G`)
has a symmetric spanner with at most `f n` edges, where `n = H.verts.ncard`. -/
theorem exists_isBigO_isSpannerOf_linear :
    ∃ f : ℕ → ℕ, (fun n ↦ (f n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ)) ∧
      ∀ {V : Type u} {G : TemporalGraph V} {H : Subgraph G} [Finite H.verts]
        [G.IsSymm] [G.IsLoopless] [H.IsSymm],
        H.IsSimple → H.IsCliqueSubgraph → H.IsProper →
        ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerOf H ∧ K.edgeSet.ncard ≤ f H.verts.ncard := by
  refine ⟨fun n ↦ 7 * n, ?_, fun h₀ h₁ h₂ ↦ exists_isSpannerOf_ncard_le_seven_mul h₀ h₁ h₂⟩
  refine IsBigO.of_bound 7 (Eventually.of_forall fun n ↦ ?_)
  simp only [Nat.cast_mul, Nat.cast_ofNat, norm_mul, Real.norm_ofNat, RCLike.norm_natCast,
    Std.le_refl]

end Bound

end Subgraph

end TemporalGraph
