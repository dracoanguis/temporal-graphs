/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Dismountability.Basic

/-!
# Extremally matched bi-cliques

Baligács 2026, §2.3. A temporal bi-clique on `s` and `t` is *extremally matched* when its earliest
edges form a perfect matching `E_min` between `s` and `t`, and so do its latest edges, `E_max`:
the earliest (resp. latest) edge at any vertex is also the earliest (resp. latest) edge at its
other endpoint. Bi-cliques without dismountable vertices are extremally matched (Lemma 5), and so
is the bi-clique between `V⁺` and `V⁻` of a clique that is not `{1,2}`-hop dismountable
(Theorem 20).

The predicate is defined once, on `TemporalGraph`, and subgraphs inherit it. The standing
assumptions of the paper (one label per edge, distinct labels at each vertex, finiteness) are not
part of it: `IsSimple`, `IsProper` and `Finite` remain separate hypotheses of the lemmas that use
them. The paper's `N_min`/`N_max` are the library's `earliestNeighborFn`/`latestNeighborFn`.

## Main definitions

* `TemporalGraph.IsExtremallyMatched` : the extremally matched temporal bi-cliques.

## Main results

* `TemporalGraph.IsExtremallyMatched.earliestNeighborFn_earliestNeighborFn`, `…latest…` :
  `N_min ∘ N_min = id` and `N_max ∘ N_max = id` on the bi-clique, in a proper graph.
* `TemporalGraph.IsExtremallyMatched.ncard_eq` : an extremally matched proper bi-clique has
  `|s| = |t|`.
* `TemporalGraph.IsExtremallyMatched.temporallyConnected` : a subgraph that contains the
  matchings `E_min`, `E_max` and in which `s` reaches `t` is temporally connected on `s ∪ t`
  (through SAND 2025's `temporallyConnected_of_reachable_of_matchings`).

## References

* Júlia Baligács, *Temporal Cliques Admit Linear Spanners*, arXiv:2606.05156v1 (2026), §2.3.
* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025
  (LIPIcs 330, doi:10.4230/LIPIcs.SAND.2025.6), §4.1.
-/

@[expose] public section

universe u

namespace TemporalGraph

variable {V : Type u} {G : TemporalGraph V} {s t : Set V}

/-- Baligács 2026, §2.3: `G` is an extremally matched temporal bi-clique on `s` and `t`: a
bi-clique in which the earliest edges form a perfect matching `E_min`, and the latest edges a
perfect matching `E_max` (the earliest, resp. latest, edge at any vertex is also the earliest,
resp. latest, edge at its other endpoint). -/
structure IsExtremallyMatched (G : TemporalGraph V) (s t : Set V) : Prop where
  isBicliqueWith : G.IsBicliqueWith s t
  earliest : ∀ v ∈ s ∪ t, ∃ w n, G.EarliestEdge v w n ∧ G.EarliestEdge w v n
  latest : ∀ v ∈ s ∪ t, ∃ w n, G.LatestEdge v w n ∧ G.LatestEdge w v n

namespace IsExtremallyMatched

variable {v : V}

/-- Extremal matching does not depend on which part is called the sources. -/
theorem symm [G.IsSymm] (h : G.IsExtremallyMatched s t) : G.IsExtremallyMatched t s where
  isBicliqueWith := h.isBicliqueWith.symm
  earliest v hv := h.earliest v hv.symm
  latest v hv := h.latest v hv.symm

/-- `N_min v` is an earliest neighbor of every vertex `v` of the bi-clique. -/
theorem earliestNeighbor_earliestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : v ∈ s ∪ t) :
    G.EarliestNeighbor v (G.earliestNeighborFn v) :=
  let ⟨w, n, h₁, _⟩ := h.earliest v h₀
  TemporalGraph.earliestNeighbor_earliestNeighborFn ⟨w, n, h₁⟩

/-- `N_max v` is a latest neighbor of every vertex `v` of the bi-clique. -/
theorem latestNeighbor_latestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : v ∈ s ∪ t) :
    G.LatestNeighbor v (G.latestNeighborFn v) :=
  let ⟨w, n, h₁, _⟩ := h.latest v h₀
  TemporalGraph.latestNeighbor_latestNeighborFn ⟨w, n, h₁⟩

/-- In a simple graph, the earliest edge at a vertex `v` of the bi-clique goes to `N_min v`, at
the `arcTime` of that arc. -/
theorem earliestEdge_earliestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsSimple)
    (h₁ : v ∈ s ∪ t) :
    G.EarliestEdge v (G.earliestNeighborFn v) (G.arcTime v (G.earliestNeighborFn v)) :=
  let ⟨w, n, h₂, _⟩ := h.earliest v h₁
  TemporalGraph.earliestEdge_earliestNeighborFn h₀ ⟨w, n, h₂⟩

/-- In a simple graph, the latest edge at a vertex `v` of the bi-clique goes to `N_max v`, at the
`arcTime` of that arc. -/
theorem latestEdge_latestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsSimple)
    (h₁ : v ∈ s ∪ t) :
    G.LatestEdge v (G.latestNeighborFn v) (G.arcTime v (G.latestNeighborFn v)) :=
  let ⟨w, n, h₂, _⟩ := h.latest v h₁
  TemporalGraph.latestEdge_latestNeighborFn h₀ ⟨w, n, h₂⟩

/-- `E_min` is a matching: `N_min (N_min v) = v`, in a proper graph. -/
theorem earliestNeighborFn_earliestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper)
    (h₁ : v ∈ s ∪ t) : G.earliestNeighborFn (G.earliestNeighborFn v) = v := by
  -- the earliest edge `v w` is also the earliest edge at `w`
  obtain ⟨w, n, h₂, h₃⟩ := h.earliest v h₁
  rw [earliestNeighborFn_eq_of_isProper h₀ ⟨n, h₂⟩, earliestNeighborFn_eq_of_isProper h₀ ⟨n, h₃⟩]

/-- `E_max` is a matching: `N_max (N_max v) = v`, in a proper graph. -/
theorem latestNeighborFn_latestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper)
    (h₁ : v ∈ s ∪ t) : G.latestNeighborFn (G.latestNeighborFn v) = v := by
  -- the latest edge `v w` is also the latest edge at `w`
  obtain ⟨w, n, h₂, h₃⟩ := h.latest v h₁
  rw [latestNeighborFn_eq_of_isProper h₀ ⟨n, h₂⟩, latestNeighborFn_eq_of_isProper h₀ ⟨n, h₃⟩]

/-- `N_min` sends a source to a target. -/
theorem earliestNeighborFn_mem_right (h : G.IsExtremallyMatched s t) (h₀ : v ∈ s) :
    G.earliestNeighborFn v ∈ t :=
  let ⟨_, h₁⟩ := h.earliestNeighbor_earliestNeighborFn (Or.inl h₀)
  h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj h₀ h₁.1

/-- `N_min` sends a target to a source. -/
theorem earliestNeighborFn_mem_left (h : G.IsExtremallyMatched s t) (h₀ : v ∈ t) :
    G.earliestNeighborFn v ∈ s :=
  let ⟨_, h₁⟩ := h.earliestNeighbor_earliestNeighborFn (Or.inr h₀)
  h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj' h₀ h₁.1

/-- `N_max` sends a source to a target. -/
theorem latestNeighborFn_mem_right (h : G.IsExtremallyMatched s t) (h₀ : v ∈ s) :
    G.latestNeighborFn v ∈ t :=
  let ⟨_, h₁⟩ := h.latestNeighbor_latestNeighborFn (Or.inl h₀)
  h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj h₀ h₁.1

/-- `N_max` sends a target to a source. -/
theorem latestNeighborFn_mem_left (h : G.IsExtremallyMatched s t) (h₀ : v ∈ t) :
    G.latestNeighborFn v ∈ s :=
  let ⟨_, h₁⟩ := h.latestNeighbor_latestNeighborFn (Or.inr h₀)
  h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj' h₀ h₁.1

/-- In a proper graph, `N_min` is injective on the bi-clique, being its own inverse there. -/
theorem injOn_earliestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper) :
    (s ∪ t).InjOn G.earliestNeighborFn := by
  intro v h₁ w h₂ h₃
  rw [← h.earliestNeighborFn_earliestNeighborFn h₀ h₁, h₃,
    h.earliestNeighborFn_earliestNeighborFn h₀ h₂]

/-- In a proper graph, `N_min` maps the sources onto the targets. -/
theorem image_earliestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper) :
    G.earliestNeighborFn '' s = t := by
  refine (Set.image_subset_iff.2 fun v h₁ ↦ h.earliestNeighborFn_mem_right h₁).antisymm
    fun u h₁ ↦ ?_
  -- a target `u` is `N_min` of the source `N_min u`
  exact ⟨G.earliestNeighborFn u, h.earliestNeighborFn_mem_left h₁,
    h.earliestNeighborFn_earliestNeighborFn h₀ (Or.inr h₁)⟩

/-- Baligács 2026, §2.3: a proper extremally matched bi-clique has as many sources as targets,
since `N_min` is a bijection between them. -/
theorem ncard_eq (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper) : s.ncard = t.ncard := by
  rw [← h.image_earliestNeighborFn h₀,
    ((h.injOn_earliestNeighborFn h₀).mono Set.subset_union_left).ncard_image]

/-- `N_min` transports the sources to the targets: for any property `P` of targets, the sources
whose `N_min` satisfies `P` are as many as the targets satisfying `P`. -/
theorem ncard_setOf_earliestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper)
    (P : V → Prop) : {v ∈ s | P (G.earliestNeighborFn v)}.ncard = {u ∈ t | P u}.ncard := by
  have h₁ : G.earliestNeighborFn '' {v ∈ s | P (G.earliestNeighborFn v)} = {u ∈ t | P u} := by
    ext u
    constructor
    · rintro ⟨v, ⟨h₂, h₃⟩, rfl⟩
      exact ⟨h.earliestNeighborFn_mem_right h₂, h₃⟩
    · rintro ⟨h₂, h₃⟩
      -- a target `u` is `N_min` of the source `N_min u`
      have h₄ := h.earliestNeighborFn_earliestNeighborFn h₀ (Or.inr h₂)
      exact ⟨G.earliestNeighborFn u, ⟨h.earliestNeighborFn_mem_left h₂, by rwa [h₄]⟩, h₄⟩
  rw [← h₁, ((h.injOn_earliestNeighborFn h₀).mono
    ((Set.sep_subset s _).trans Set.subset_union_left)).ncard_image]

/-- Every vertex of an extremally matched bi-clique carries an edge, so lies in `H.verts`. -/
theorem subset_verts {H : Subgraph G} (h : H.IsExtremallyMatched s t) : s ∪ t ⊆ H.verts :=
  fun v h₀ ↦ let ⟨_, _, h₁, _⟩ := h.earliest v h₀; H.edge_vert h₁.1

/-- Baligács 2026, Theorem 18 (second part): a subgraph `K` of an extremally matched bi-clique
`H` that contains the matchings `E_min` and `E_max`, and in which every source reaches every
target, is temporally connected on `s ∪ t`. The earliest (resp. latest) edges of `H` stay earliest
(resp. latest) in `K`, so SAND 2025's `temporallyConnected_of_reachable_of_matchings` applies. -/
theorem temporallyConnected {H K : Subgraph G} [K.IsSymm] (h : H.IsExtremallyMatched s t)
    (h₀ : K ≤ H) (h₁ : ∀ v ∈ s ∪ t, ∀ w n, H.EarliestEdge v w n → K.Adj v w n)
    (h₂ : ∀ v ∈ s ∪ t, ∀ w n, H.LatestEdge v w n → K.Adj v w n)
    (h₃ : ∀ x ∈ s, ∀ y ∈ t, K.Reachable x y) : K.TemporallyConnected (s ∪ t) := by
  refine temporallyConnected_of_reachable_of_matchings (fun b hb ↦ ?_) (fun y hy ↦ ?_) h₃
  · -- the earliest edge at `b ∈ t` goes to a source `w`, and it is the earliest edge at `w`
    obtain ⟨w, n, h₄, h₅⟩ := h.earliest b (Or.inr hb)
    have hw : w ∈ s := h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj' hb h₄.1
    exact ⟨w, hw, n, Subgraph.earliestEdge_of_ge h₀ h₅ (h₁ w (Or.inl hw) b n h₅)⟩
  · -- the latest edge at `y ∈ s` goes to a target `w`, and it is the latest edge at `w`
    obtain ⟨w, n, h₄, h₅⟩ := h.latest y (Or.inl hy)
    have hw : w ∈ t := h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj hy h₄.1
    exact ⟨w, hw, n, Subgraph.latestEdge_of_ge h₀ h₅ (h₂ w (Or.inr hw) y n h₅)⟩

end IsExtremallyMatched

end TemporalGraph
