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
them. The paper's `N_min`/`N_max` are the library's `earliestNeighborFn`/`latestNeighborFn`,
whose values are `Option`s (`none` for a vertex without edges); on the bi-clique they are always
`some`.

## Main definitions

* `TemporalGraph.IsExtremallyMatched` : the extremally matched temporal bi-cliques.

## Main results

* `TemporalGraph.IsExtremallyMatched.earliestNeighborFn_eq_some_symm`,
  `TemporalGraph.IsExtremallyMatched.latestNeighborFn_eq_some_symm` : `E_min` and `E_max` are
  matchings: `N_min v = some w → N_min w = some v` (and likewise for `N_max`), in a proper graph.
* `TemporalGraph.IsExtremallyMatched.ncard_eq` : an extremally matched proper bi-clique has
  `|s| = |t|`.
* `TemporalGraph.IsExtremallyMatched.induce`, `TemporalGraph.isExtremallyMatched_induce_empty` :
  restricting to the parts keeps the extremal matching; the empty bi-clique is extremally matched.
* `TemporalGraph.IsExtremallyMatched.arcTime_le_of_earliestNeighborFn_eq_some`,
  `TemporalGraph.IsExtremallyMatched.arcTime_le_of_latestNeighborFn_eq_some` : the matched edges
  are the earliest (resp. latest) at both of their endpoints, read on `arcTime`.
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
  /-- `G` is a temporal bi-clique on `s` and `t`. -/
  isBicliqueWith : G.IsBicliqueWith s t
  /-- The earliest edge at any vertex is also the earliest edge at its other endpoint. -/
  earliest : ∀ v ∈ s ∪ t, ∃ w n, G.EarliestEdge v w n ∧ G.EarliestEdge w v n
  /-- The latest edge at any vertex is also the latest edge at its other endpoint. -/
  latest : ∀ v ∈ s ∪ t, ∃ w n, G.LatestEdge v w n ∧ G.LatestEdge w v n

namespace IsExtremallyMatched

variable {v w : V}

/-- Extremal matching does not depend on which part is called the sources. -/
theorem symm [G.IsSymm] (h : G.IsExtremallyMatched s t) : G.IsExtremallyMatched t s where
  isBicliqueWith := h.isBicliqueWith.symm
  earliest v hv := h.earliest v hv.symm
  latest v hv := h.latest v hv.symm

/-- `N_min` is defined on every vertex of the bi-clique. -/
theorem exists_earliestNeighborFn_eq_some (h : G.IsExtremallyMatched s t) (h₀ : v ∈ s ∪ t) :
    ∃ w, G.earliestNeighborFn v = some w :=
  let ⟨w, n, h₁, _⟩ := h.earliest v h₀
  Option.isSome_iff_exists.1 (earliestNeighborFn_isSome_iff.2 ⟨w, n, h₁⟩)

/-- `N_max` is defined on every vertex of the bi-clique. -/
theorem exists_latestNeighborFn_eq_some (h : G.IsExtremallyMatched s t) (h₀ : v ∈ s ∪ t) :
    ∃ w, G.latestNeighborFn v = some w :=
  let ⟨w, n, h₁, _⟩ := h.latest v h₀
  Option.isSome_iff_exists.1 (latestNeighborFn_isSome_iff.2 ⟨w, n, h₁⟩)

/-- `E_min` is a matching: in a proper graph, if `N_min v = w` then `N_min w = v`. -/
theorem earliestNeighborFn_eq_some_symm (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper)
    (h₁ : v ∈ s ∪ t) (h₂ : G.earliestNeighborFn v = some w) : G.earliestNeighborFn w = some v := by
  -- the earliest edge `v w'` is also the earliest edge at `w'`, and `w' = w`
  obtain ⟨w', n, h₃, h₄⟩ := h.earliest v h₁
  rw [earliestNeighborFn_eq_some h₀ ⟨n, h₃⟩, Option.some_inj] at h₂
  exact h₂ ▸ earliestNeighborFn_eq_some h₀ ⟨n, h₄⟩

/-- `E_max` is a matching: in a proper graph, if `N_max v = w` then `N_max w = v`. -/
theorem latestNeighborFn_eq_some_symm (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper)
    (h₁ : v ∈ s ∪ t) (h₂ : G.latestNeighborFn v = some w) : G.latestNeighborFn w = some v := by
  -- the latest edge `v w'` is also the latest edge at `w'`, and `w' = w`
  obtain ⟨w', n, h₃, h₄⟩ := h.latest v h₁
  rw [latestNeighborFn_eq_some h₀ ⟨n, h₃⟩, Option.some_inj] at h₂
  exact h₂ ▸ latestNeighborFn_eq_some h₀ ⟨n, h₄⟩

/-- `N_min` sends a source to a target. -/
theorem mem_right_of_earliestNeighborFn_eq_some (h : G.IsExtremallyMatched s t) (h₀ : v ∈ s)
    (h₁ : G.earliestNeighborFn v = some w) : w ∈ t :=
  let ⟨_, h₂⟩ := earliestNeighbor_of_earliestNeighborFn_eq_some h₁
  h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj h₀ h₂.1

/-- `N_min` sends a target to a source. -/
theorem mem_left_of_earliestNeighborFn_eq_some (h : G.IsExtremallyMatched s t) (h₀ : v ∈ t)
    (h₁ : G.earliestNeighborFn v = some w) : w ∈ s :=
  let ⟨_, h₂⟩ := earliestNeighbor_of_earliestNeighborFn_eq_some h₁
  h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj' h₀ h₂.1

/-- `N_max` sends a source to a target. -/
theorem mem_right_of_latestNeighborFn_eq_some (h : G.IsExtremallyMatched s t) (h₀ : v ∈ s)
    (h₁ : G.latestNeighborFn v = some w) : w ∈ t :=
  let ⟨_, h₂⟩ := latestNeighbor_of_latestNeighborFn_eq_some h₁
  h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj h₀ h₂.1

/-- `N_max` sends a target to a source. -/
theorem mem_left_of_latestNeighborFn_eq_some (h : G.IsExtremallyMatched s t) (h₀ : v ∈ t)
    (h₁ : G.latestNeighborFn v = some w) : w ∈ s :=
  let ⟨_, h₂⟩ := latestNeighbor_of_latestNeighborFn_eq_some h₁
  h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj' h₀ h₂.1

/-- In a proper graph, `N_min` is injective on the bi-clique: it is an involution there. -/
theorem injOn_earliestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper) :
    (s ∪ t).InjOn G.earliestNeighborFn := by
  intro v h₁ v' h₂ h₃
  obtain ⟨w, h₄⟩ := h.exists_earliestNeighborFn_eq_some h₁
  -- `v` and `v'` are both the earliest neighbor of `w`
  exact Option.some_injective _ ((h.earliestNeighborFn_eq_some_symm h₀ h₁ h₄).symm.trans
    (h.earliestNeighborFn_eq_some_symm h₀ h₂ (h₃ ▸ h₄)))

/-- In a proper graph, `N_min` maps the sources onto the targets. -/
theorem image_earliestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper) :
    G.earliestNeighborFn '' s = some '' t := by
  ext o
  constructor
  · rintro ⟨v, h₁, rfl⟩
    obtain ⟨w, h₂⟩ := h.exists_earliestNeighborFn_eq_some (Or.inl h₁)
    exact ⟨w, h.mem_right_of_earliestNeighborFn_eq_some h₁ h₂, h₂.symm⟩
  · rintro ⟨u, h₁, rfl⟩
    -- a target `u` is `N_min` of the source `N_min u`
    obtain ⟨v, h₂⟩ := h.exists_earliestNeighborFn_eq_some (Or.inr h₁)
    exact ⟨v, h.mem_left_of_earliestNeighborFn_eq_some h₁ h₂,
      h.earliestNeighborFn_eq_some_symm h₀ (Or.inr h₁) h₂⟩

/-- Baligács 2026, §2.3: a proper extremally matched bi-clique has as many sources as targets,
since `N_min` is a bijection between them. -/
theorem ncard_eq (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper) : s.ncard = t.ncard := by
  rw [← Set.ncard_image_of_injective t (Option.some_injective V), ← h.image_earliestNeighborFn h₀,
    ((h.injOn_earliestNeighborFn h₀).mono Set.subset_union_left).ncard_image]

/-- `N_min` maps the sources whose `N_min` satisfies `P` onto the targets satisfying `P`. -/
private theorem image_setOf_earliestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper)
    (P : V → Prop) :
    G.earliestNeighborFn '' {v ∈ s | ∃ w ∈ G.earliestNeighborFn v, P w} =
      some '' {u ∈ t | P u} := by
  ext o
  constructor
  · rintro ⟨v, ⟨h₂, w, h₃, h₄⟩, rfl⟩
    rw [Option.mem_def] at h₃
    exact ⟨w, ⟨h.mem_right_of_earliestNeighborFn_eq_some h₂ h₃, h₄⟩, h₃.symm⟩
  · rintro ⟨u, ⟨h₂, h₃⟩, rfl⟩
    -- a target `u` is `N_min` of the source `N_min u`
    obtain ⟨v, h₄⟩ := h.exists_earliestNeighborFn_eq_some (Or.inr h₂)
    have h₅ := h.earliestNeighborFn_eq_some_symm h₀ (Or.inr h₂) h₄
    exact ⟨v, ⟨h.mem_left_of_earliestNeighborFn_eq_some h₂ h₄, u, h₅, h₃⟩, h₅⟩

/-- `N_min` transports the sources to the targets: for any property `P` of targets, the sources
whose `N_min` satisfies `P` are as many as the targets satisfying `P`. -/
theorem ncard_setOf_earliestNeighborFn (h : G.IsExtremallyMatched s t) (h₀ : G.IsProper)
    (P : V → Prop) :
    {v ∈ s | ∃ w ∈ G.earliestNeighborFn v, P w}.ncard = {u ∈ t | P u}.ncard := by
  calc {v ∈ s | ∃ w ∈ G.earliestNeighborFn v, P w}.ncard
      = (G.earliestNeighborFn '' {v ∈ s | ∃ w ∈ G.earliestNeighborFn v, P w}).ncard :=
        ((h.injOn_earliestNeighborFn h₀).mono
          ((Set.sep_subset s _).trans Set.subset_union_left)).ncard_image.symm
    _ = {u ∈ t | P u}.ncard := by
        rw [h.image_setOf_earliestNeighborFn h₀ P,
          Set.ncard_image_of_injective _ (Option.some_injective V)]

/-- Every vertex of an extremally matched bi-clique carries an edge, so lies in `H.verts`. -/
theorem subset_verts {H : Subgraph G} (h : H.IsExtremallyMatched s t) : s ∪ t ⊆ H.verts :=
  fun v h₀ ↦ let ⟨_, _, h₁, _⟩ := h.earliest v h₀; H.edge_vert h₁.1

/-- The sources of an extremally matched bi-clique of a finite subgraph are finitely many. -/
theorem finite_left {H : Subgraph G} [Finite H.verts] (h : H.IsExtremallyMatched s t) :
    s.Finite :=
  (Set.toFinite H.verts).subset (Set.subset_union_left.trans h.subset_verts)

/-- The targets of an extremally matched bi-clique of a finite subgraph are finitely many. -/
theorem finite_right {H : Subgraph G} [Finite H.verts] (h : H.IsExtremallyMatched s t) :
    t.Finite :=
  (Set.toFinite H.verts).subset (Set.subset_union_right.trans h.subset_verts)

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
    exact ⟨w, hw, n, Subgraph.earliestEdge_of_le h₀ h₅ (h₁ w (Or.inl hw) b n h₅)⟩
  · -- the latest edge at `y ∈ s` goes to a target `w`, and it is the latest edge at `w`
    obtain ⟨w, n, h₄, h₅⟩ := h.latest y (Or.inl hy)
    have hw : w ∈ t := h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj hy h₄.1
    exact ⟨w, hw, n, Subgraph.latestEdge_of_le h₀ h₅ (h₂ w (Or.inr hw) y n h₅)⟩

/-- An extremally matched bi-clique stays extremally matched when restricted to its own parts:
the matched edges of `s ∪ t` stay inside `s ∪ t`, so they remain earliest and latest edges. -/
theorem induce {H : Subgraph G} (h : H.IsExtremallyMatched s t) :
    (H.induce (s ∪ t)).IsExtremallyMatched s t := by
  have h₀ : H.induce (s ∪ t) ≤ H := Subgraph.induce_le_of_subset h.subset_verts
  -- an edge at a vertex of `s ∪ t` ends in `s ∪ t`, since the graph is bipartite on `s`, `t`
  have h₁ : ∀ {v w : V} {n : ℕ}, v ∈ s ∪ t → H.Adj v w n → w ∈ s ∪ t := by
    rintro v w n (hv | hv) hadj
    · exact Or.inr (h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj hv hadj)
    · exact Or.inl (h.isBicliqueWith.isBipartiteWith.mem_of_mem_adj' hv hadj)
  refine ⟨Subgraph.isBicliqueWith_induce h.isBicliqueWith subset_rfl subset_rfl, fun v hv ↦ ?_,
    fun v hv ↦ ?_⟩
  · obtain ⟨w, n, h₂, h₃⟩ := h.earliest v hv
    have hw := h₁ hv h₂.1
    exact ⟨w, n, Subgraph.earliestEdge_of_le h₀ h₂ ⟨hv, hw, h₂.1⟩,
      Subgraph.earliestEdge_of_le h₀ h₃ ⟨hw, hv, h₃.1⟩⟩
  · obtain ⟨w, n, h₂, h₃⟩ := h.latest v hv
    have hw := h₁ hv h₂.1
    exact ⟨w, n, Subgraph.latestEdge_of_le h₀ h₂ ⟨hv, hw, h₂.1⟩,
      Subgraph.latestEdge_of_le h₀ h₃ ⟨hw, hv, h₃.1⟩⟩

section Times

variable {y : V} {a b : ℕ}

/-- In a simple graph, a source has an arc, with a defined time, to each target. -/
theorem exists_arcTime_eq_some_left (h : G.IsExtremallyMatched s t) (h₀ : G.IsSimple)
    (h₁ : v ∈ s) (h₂ : y ∈ t) : ∃ n, G.arcTime v y = some n :=
  let ⟨n, h₃⟩ := h.isBicliqueWith.adj_of_mem h₁ h₂
  ⟨n, arcTime_eq_some h₀ h₃⟩

/-- In a symmetric simple graph, a target has an arc, with a defined time, to each source. -/
theorem exists_arcTime_eq_some_right [G.IsSymm] (h : G.IsExtremallyMatched s t)
    (h₀ : G.IsSimple) (h₁ : v ∈ t) (h₂ : y ∈ s) : ∃ n, G.arcTime v y = some n :=
  (arcTime_comm h₀ v y).symm ▸ h.exists_arcTime_eq_some_left h₀ h₂ h₁

/-- In a simple proper graph, the earliest edge at a vertex `v` of the bi-clique, to
`N_min v = w`, is also the earliest edge at `w`, and happens at the `arcTime` of the arc. -/
theorem exists_earliestEdge_of_earliestNeighborFn_eq_some (h : G.IsExtremallyMatched s t)
    (h₀ : G.IsSimple) (h₁ : G.IsProper) (h₂ : v ∈ s ∪ t) (h₃ : G.earliestNeighborFn v = some w) :
    ∃ n, G.arcTime v w = some n ∧ G.EarliestEdge v w n ∧ G.EarliestEdge w v n := by
  obtain ⟨w', n, h₄, h₅⟩ := h.earliest v h₂
  -- the matched earliest edge goes to `N_min v`, so `w' = w`
  obtain rfl : w' = w := Option.some_inj.1 ((h₄.earliestNeighborFn_eq_some h₁).symm.trans h₃)
  exact ⟨n, h₄.arcTime_eq_some h₀, h₄, h₅⟩

/-- In a simple proper graph, the latest edge at a vertex `v` of the bi-clique, to
`N_max v = w`, is also the latest edge at `w`, and happens at the `arcTime` of the arc. -/
theorem exists_latestEdge_of_latestNeighborFn_eq_some (h : G.IsExtremallyMatched s t)
    (h₀ : G.IsSimple) (h₁ : G.IsProper) (h₂ : v ∈ s ∪ t) (h₃ : G.latestNeighborFn v = some w) :
    ∃ n, G.arcTime v w = some n ∧ G.LatestEdge v w n ∧ G.LatestEdge w v n := by
  obtain ⟨w', n, h₄, h₅⟩ := h.latest v h₂
  -- the matched latest edge goes to `N_max v`, so `w' = w`
  obtain rfl : w' = w := Option.some_inj.1 ((h₄.latestNeighborFn_eq_some h₁).symm.trans h₃)
  exact ⟨n, h₄.arcTime_eq_some h₀, h₄, h₅⟩

/-- The edge `{v, N_min v}`, at time `a`, is the earliest edge at `N_min v`: no arc leaving
`N_min v` is earlier. -/
theorem arcTime_le_of_earliestNeighborFn_eq_some (h : G.IsExtremallyMatched s t)
    (h₀ : G.IsSimple) (h₁ : G.IsProper) (h₂ : v ∈ s ∪ t) (h₃ : G.earliestNeighborFn v = some w)
    (h₄ : G.arcTime v w = some a) (h₅ : G.arcTime w y = some b) : a ≤ b := by
  obtain ⟨n, h₆, -, h₇⟩ := h.exists_earliestEdge_of_earliestNeighborFn_eq_some h₀ h₁ h₂ h₃
  exact Option.some_inj.1 (h₄.symm.trans h₆) ▸ h₇.2 y b (adj_of_arcTime_eq_some h₅)

/-- The edge `{v, N_max v}`, at time `a`, is the latest edge at `N_max v`: no arc leaving
`N_max v` is later. -/
theorem arcTime_le_of_latestNeighborFn_eq_some (h : G.IsExtremallyMatched s t)
    (h₀ : G.IsSimple) (h₁ : G.IsProper) (h₂ : v ∈ s ∪ t) (h₃ : G.latestNeighborFn v = some w)
    (h₄ : G.arcTime v w = some a) (h₅ : G.arcTime w y = some b) : b ≤ a := by
  obtain ⟨n, h₆, -, h₇⟩ := h.exists_latestEdge_of_latestNeighborFn_eq_some h₀ h₁ h₂ h₃
  exact Option.some_inj.1 (h₄.symm.trans h₆) ▸ h₇.2 y b (adj_of_arcTime_eq_some h₅)

end Times

end IsExtremallyMatched

/-- The empty bi-clique, induced on no vertex, is (vacuously) extremally matched. -/
theorem isExtremallyMatched_induce_empty {H : Subgraph G} :
    (H.induce ∅).IsExtremallyMatched (∅ : Set V) ∅ where
  isBicliqueWith :=
    { isBipartiteWith :=
        { disjoint := disjoint_bot_left
          mem_of_adj := fun _ _ _ h ↦ absurd h.1 (Set.notMem_empty _) }
      adj_of_mem := fun _ _ h ↦ absurd h (Set.notMem_empty _) }
  earliest v hv := by simp only [Set.union_empty, Set.mem_empty_iff_false] at hv
  latest v hv := by simp only [Set.union_empty, Set.mem_empty_iff_false] at hv

end TemporalGraph
