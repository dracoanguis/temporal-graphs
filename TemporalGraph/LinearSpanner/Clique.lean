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

section Theorem20

/-- An earliest edge `a b` of `a ∈ V⁺` to `b ∈ V⁻` is the earliest edge at both ends in the
bi-clique `H.between V⁻ V⁺`, in a clique that is not `{1,2}`-hop dismountable. -/
private theorem earliestEdge_between_of_earliestEdge_vplus {H : Subgraph G}
    [H.IsSymm] {a b : V} {n : ℕ} (h₀ : H.IsCliqueSubgraph)
    (h₁ : ¬H.TwoHopDismountable) (h₂ : a ∈ H.vplus) (h₃ : b ∈ H.vminus)
    (h₄ : H.EarliestEdge a b n) :
    (H.between H.vminus H.vplus).EarliestEdge a b n ∧
      (H.between H.vminus H.vplus).EarliestEdge b a n := by
  have hdisj : Disjoint H.vminus H.vplus :=
    (biclique_of_not_twoHopDismountable h₀ h₁).isBipartiteWith.disjoint
  -- `between A B` has the arcs of `H` going from `A` to `B` or from `B` to `A`
  have hab : (H.between H.vminus H.vplus).Adj a b n := ⟨h₄.1, Or.inr ⟨h₂, h₃⟩⟩
  refine ⟨earliestEdge_of_le between_le h₄ hab, ⟨hab.symm, fun z m hz ↦ ?_⟩⟩
  -- the edges of `b ∈ V⁻` in the bi-clique go to `V⁺`, where reciprocity bounds the time
  have hzp : z ∈ H.vplus := by
    rcases hz.2 with ⟨-, hz⟩ | ⟨hb', -⟩
    · -- orientation `b ∈ V⁻`, `z ∈ V⁺`
      exact hz
    · -- orientation `b ∈ V⁺`, `z ∈ V⁻`: impossible, `b ∈ V⁻` and `V⁻`, `V⁺` are disjoint
      exact absurd hb' (Set.disjoint_left.mp hdisj h₃)
  exact earliestEdge_reciprocity h₀ h₁ h₄ z hzp m hz.1

/-- A latest edge `a b` of `a ∈ V⁻` to `b ∈ V⁺` is the latest edge at both ends in the bi-clique
`H.between V⁻ V⁺`, in a clique that is not `{1,2}`-hop dismountable. -/
private theorem latestEdge_between_of_latestEdge_vminus {H : Subgraph G}
    [H.IsSymm] {a b : V} {n : ℕ} (h₀ : H.IsCliqueSubgraph)
    (h₁ : ¬H.TwoHopDismountable) (h₂ : a ∈ H.vminus) (h₃ : b ∈ H.vplus)
    (h₄ : H.LatestEdge a b n) :
    (H.between H.vminus H.vplus).LatestEdge a b n ∧
      (H.between H.vminus H.vplus).LatestEdge b a n := by
  have hdisj : Disjoint H.vminus H.vplus :=
    (biclique_of_not_twoHopDismountable h₀ h₁).isBipartiteWith.disjoint
  have hab : (H.between H.vminus H.vplus).Adj a b n := ⟨h₄.1, Or.inl ⟨h₂, h₃⟩⟩
  refine ⟨latestEdge_of_le between_le h₄ hab, ⟨hab.symm, fun z m hz ↦ ?_⟩⟩
  -- the edges of `b ∈ V⁺` in the bi-clique go to `V⁻`, where reciprocity bounds the time
  have hzm : z ∈ H.vminus := by
    rcases hz.2 with ⟨hb', -⟩ | ⟨-, hz⟩
    · -- orientation `b ∈ V⁻`, `z ∈ V⁺`: impossible, `b ∈ V⁺` and `V⁻`, `V⁺` are disjoint
      exact absurd hb' (Set.disjoint_right.mp hdisj h₃)
    · -- orientation `b ∈ V⁺`, `z ∈ V⁻`
      exact hz
  exact latestEdge_reciprocity h₀ h₁ h₄ z hzm m hz.1

/-- Baligács 2026, Theorem 20: in a finite simple proper clique `H` that is not `{1,2}`-hop
dismountable, the bi-clique `H.between V⁻ V⁺` is extremally matched, with sources `V⁺` and targets
`V⁻` (the order is swapped relative to `between`). The earliest edge of a vertex of `V⁻` comes from
`V⁺` (SAND 2025, Corollary 3.3), and by reciprocity (SAND 2025, Lemma 3.5) it is also the earliest
edge of its other endpoint; likewise for the latest edges. -/
theorem isExtremallyMatched_between_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) (h₃ : ¬H.TwoHopDismountable) :
    (H.between H.vminus H.vplus).IsExtremallyMatched H.vplus H.vminus := by
  refine ⟨(biclique_of_not_twoHopDismountable h₁ h₃).symm, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · rcases hv with hv | hv
    · -- `v ∈ V⁺`: its earliest edge goes to `V⁻`
      obtain ⟨b, n, h⟩ := exists_earliestEdge_of_isCliqueSubgraph h₀ h₁ v
        (vplus_subset_verts hv)
      have hb := earliestNeighbor_mem_vminus ⟨n, h⟩
      have hboth := earliestEdge_between_of_earliestEdge_vplus h₁ h₃ hv hb h
      exact ⟨b, n, hboth.1, hboth.2⟩
    · -- `v ∈ V⁻`: SAND 2025, Corollary 3.3, a unique earliest edge from `V⁺`
      obtain ⟨⟨a, n⟩, ⟨ha, h⟩, -⟩ := existsUnique_vplus_earliestEdge h₀ h₁ h₂ h₃ v hv
      have hboth := earliestEdge_between_of_earliestEdge_vplus h₁ h₃ ha hv h
      exact ⟨a, n, hboth.2, hboth.1⟩
  · rcases hv with hv | hv
    · -- `v ∈ V⁺`: SAND 2025, Corollary 3.3, a unique latest edge from `V⁻`
      obtain ⟨⟨a, n⟩, ⟨ha, h⟩, -⟩ := existsUnique_vminus_latestEdge h₀ h₁ h₂ h₃ v hv
      have hboth := latestEdge_between_of_latestEdge_vminus h₁ h₃ ha hv h
      exact ⟨a, n, hboth.2, hboth.1⟩
    · -- `v ∈ V⁻`: its latest edge goes to `V⁺`
      obtain ⟨b, n, h⟩ := exists_latestEdge_of_isCliqueSubgraph h₀ h₁ v
        (vminus_subset_verts hv)
      have hb := latestNeighbor_mem_vplus ⟨n, h⟩
      have hboth := latestEdge_between_of_latestEdge_vminus h₁ h₃ hv hb h
      exact ⟨b, n, hboth.1, hboth.2⟩

end Theorem20

section LinearBound

/-- Baligács 2026, §5 (non-dismountable case of Theorem 2): a finite simple proper clique `H`
that is not `{1,2}`-hop dismountable has a symmetric spanner with at most `7 n` edges, where
`n = |H.verts|`.

Proof: by Theorem 20, `H.between V⁻ V⁺` is extremally matched, and Theorem 18 gives a spanner of
it, temporally connected on `V⁺ ∪ V⁻ = H.verts` (SAND 2025, Lemma 3.4), with at most
`14 |V⁺| = 7 n` edges (SAND 2025, Corollary 3.3 (3)). -/
theorem exists_isSpannerOf_ncard_le_seven_mul_of_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [Nontrivial H.verts] [G.IsSymm] [G.IsLoopless] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) (h₃ : ¬H.TwoHopDismountable) :
    ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerOf H ∧ K.edgeSet.ncard ≤ 7 * H.verts.ncard := by
  have hem := isExtremallyMatched_between_of_not_twoHopDismountable h₀ h₁ h₂ h₃
  have hBle : H.between H.vminus H.vplus ≤ H := between_le
  have : Finite (H.between H.vminus H.vplus).verts := inferInstanceAs (Finite H.verts)
  -- Theorem 18 on the bi-clique, with sources `V⁺`
  obtain ⟨K, hKsymm, hKspan, hKtc, hKcard⟩ := hem.exists_isSpannerFromTo_temporallyConnected
    (h₀.mono (toTemporalGraph_le hBle)) (h₂.mono (toTemporalGraph_le hBle))
  -- `V⁻ ∪ V⁺ ∪ V⁰ = H.verts` and `V⁰ = ∅` (SAND 2025, Lemma 3.4), so `H.verts = V⁺ ∪ V⁻`
  have hverts : H.verts = H.vplus ∪ H.vminus := by
    rw [Set.union_comm, ← vminus_union_vplus_union_vzero,
      vzero_empty_of_not_twoHopDismountable h₀ h₁ h₂ h₃, Set.union_empty]
  have hdisj := (biclique_of_not_twoHopDismountable h₁ h₃).isBipartiteWith.disjoint
  have hcard := vminus_card_eq_vplus_card h₀ h₁ h₃
  have hn : H.verts.ncard = 2 * H.vplus.ncard := by
    rw [hverts, Set.ncard_union_eq hdisj.symm
      ((Set.toFinite H.verts).subset vplus_subset_verts)
      ((Set.toFinite H.verts).subset vminus_subset_verts)]
    -- `|V⁺| + |V⁻| = 2 |V⁺|`, as `|V⁻| = |V⁺|`
    omega
  refine ⟨K, hKsymm, isSpannerOf_of_le_of_temporallyConnected (hKspan.1.trans hBle) ?_, ?_⟩
  · rwa [hverts]
  · -- `|K| ≤ 14 |V⁺| = 7 (2 |V⁺|) = 7 n`
    omega

/-- Baligács 2026, Theorem 2: every finite simple proper temporal clique on `n` vertices admits
a symmetric spanner with at most `7 n` edges. This is SAND 2025, Theorem 2.1 and §2.1 (the
generic induction `exists_isSpannerOf_ncard_le_of_forall_not_twoHopDismountable`, each dismounted
vertex costing 4 edges, at most the slope 7), with the non-dismountable case Theorem 18 (see
`exists_isSpannerOf_ncard_le_seven_mul_of_not_twoHopDismountable`). -/
theorem exists_isSpannerOf_ncard_le_seven_mul {H : Subgraph G} [Finite H.verts]
    [G.IsSymm] [G.IsLoopless] [H.IsSymm]
    (h₀ : H.IsSimple) (h₁ : H.IsCliqueSubgraph) (h₂ : H.IsProper) :
    ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerOf H ∧ K.edgeSet.ncard ≤ 7 * H.verts.ncard :=
  exists_isSpannerOf_ncard_le_of_forall_not_twoHopDismountable (fun n ↦ 7 * n) (fun n ↦ by omega)
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
  -- `‖7 n‖ ≤ 7 ‖n‖`
  refine IsBigO.of_bound 7 (Eventually.of_forall fun n ↦ ?_)
  simp only [Nat.cast_mul, Nat.cast_ofNat, norm_mul, Real.norm_ofNat, RCLike.norm_natCast,
    Std.le_refl]

end LinearBound

end Subgraph

end TemporalGraph
