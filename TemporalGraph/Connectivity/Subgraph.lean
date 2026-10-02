/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Connectivity.Basic
import TemporalGraph.Subgraph

/-!
# Subgraph Reachability and Spanners

Extends reachability and connectivity concepts to subgraphs. `Reachable` and
`TemporallyConnected` are no longer redefined here: `Subgraph` extends `TemporalGraph V`, so
`H.Reachable x y` (for `x y : V`) and `H.TemporallyConnected S` resolve through generalized
field notation to the parent notions taken at `H.toTemporalGraph`. `TemporallyConnectedSubgraph`
abbreviates `H.TemporallyConnected H.verts`, as `IsCliqueSubgraph` does for `IsClique`.

Defines spanner types: `IsSpanner` (reachability-preserving), `IsSpannerOf` (one subgraph as
spanner of another), and `IsTCSpanner` (temporally connected spanner).

## Main definitions
* `IsSpanner` : A spanning subgraph that preserves reachability
* `IsSpannerOf` : One subgraph spanning and preserving reachability in another
* `IsTCSpanner` : A temporally connected spanner
* `TemporallyConnectedSubgraph` : abbreviation for `H.TemporallyConnected H.verts`

## Main results
* `reachable_of_subgraph_reachable` : Reachability in subgraph implies reachability in parent
* `reachable_of_le_reachable` : Reachability preserved under subgraph inclusion
* `TCspanner_iff_TC` : Existence of a TC-spanner characterizes temporal connectivity
* `mem_verts_of_reachable` : A reachable pair of distinct vertices lies in `H`'s own vertex set
* `top_isSpanner` : The whole graph `⊤` is a spanner of itself
* `addVerts_reachability`, `addEdge_reachability`, `deleteVerts_reachability` : reachability is
  preserved by these subgraph constructions
-/

universe u
variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

namespace Subgraph

section Spanners

/-- A `Subgraph` is a spanner of its original graph `G`, if it's spanning and every pair of its
vertices has the same reachability as in `G`. -/
def IsSpanner (H : Subgraph G) : Prop :=
  H.IsSpanning ∧ ∀ x ∈ H.verts, ∀ y ∈ H.verts, G.Reachable x y → H.Reachable x y

/-- A `Subgraph` `H` is a spanner of another one `H'` if they have the same vertices and
everything reachable in `H'` is also in `H`. -/
def IsSpannerOf (H : Subgraph G) (H' : Subgraph G) : Prop :=
  H ≤ H' ∧ H.verts = H'.verts ∧ ∀ x ∈ H'.verts, ∀ y ∈ H'.verts, H'.Reachable x y → H.Reachable x y

end Spanners

section TemporalConnectivity

/-- `H` is temporally connected on its own vertex set. Shorthand for
`H.TemporallyConnected H.verts`. -/
abbrev TemporallyConnectedSubgraph (H : Subgraph G) : Prop :=
  H.TemporallyConnected H.verts

/-- The `Subgraph` `H` is a temporally connected spanner of `G`
if it is spanning and it is temporally connected. -/
def IsTCSpanner (H : Subgraph G) : Prop :=
  (H.IsSpanning) ∧ (H.TemporallyConnectedSubgraph)

/-- `H.IsTCSpanner` is equivalent to `H.IsSpanner ∧ H.TemporallyConnectedSubgraph`: once `H` is
temporally connected on its own vertices, the spanner condition holds vacuously (`H.Reachable x y`
already holds, regardless of `G.Reachable x y`). -/
theorem isTCSpanner_iff_isSpanner_and_TC {H : Subgraph G} :
    H.IsTCSpanner ↔ H.IsSpanner ∧ H.TemporallyConnectedSubgraph := by
  unfold IsTCSpanner IsSpanner
  constructor
  · intro ⟨h_span, h_tc⟩
    exact ⟨⟨h_span, fun x hx y hy _ ↦ h_tc x hx y hy⟩, h_tc⟩
  · intro ⟨⟨h_span, _⟩, h_tc⟩
    exact ⟨h_span, h_tc⟩

end TemporalConnectivity

section ReachabilityPreservation

/-- A reachable pair of distinct vertices lies in `H`'s own vertex set: a walk witnessing the
reachability is nonempty (`x ≠ y` rules out `TemporalWalk.Empty`), and its first and last arcs
give each endpoint's membership. -/
lemma mem_verts_of_reachable {H : Subgraph G} {x y : V} (h₀ : H.Reachable x y) (h₁ : x ≠ y) :
    x ∈ H.verts ∧ y ∈ H.verts := by
  obtain ⟨n, m, ⟨w⟩⟩ := h₀
  cases w with
  | Empty => exact absurd rfl h₁
  | Nonempty p =>
    obtain ⟨z, j, hz⟩ := p.exists_adj_fst
    obtain ⟨z', j', hz'⟩ := p.exists_adj_snd
    exact ⟨H.edge_vert hz, H.edge_vert' hz'⟩

/-- Reachability in a subgraph implies reachability in the ambient graph. -/
lemma reachable_of_subgraph_reachable {H : Subgraph G} {x y : V} :
    H.Reachable x y → G.Reachable x y :=
  Reachable.mono H.toTemporalGraph_le_self

/-- Reachability is preserved along subgraph inclusion. -/
lemma reachable_of_le_reachable {H H' : Subgraph G} (h : H ≤ H') {x y : V} :
    H.Reachable x y → H'.Reachable x y :=
  Reachable.mono (toTemporalGraph_le h)

/-- If `H` is spanning and temporally connected on its own vertices, then `H`'s own adjacency
(`H.toTemporalGraph`) is temporally connected on all of `V`: spanning turns the quantification
over `H.verts` into one over `Set.univ`. -/
lemma toTemporalGraph_temporallyConnected_of_spanning_temporallyConnected
    {H : Subgraph G} :
    H.TemporallyConnectedSubgraph ∧ H.IsSpanning → H.toTemporalGraph.TemporallyConnectedGraph := by
  intro ⟨h_tc, h_span⟩
  intro x _ y _
  exact h_tc x (h_span x) y (h_span y)

/-- A TC-spanner of `G` witnesses that `G` itself is temporally connected: reachability in `H`
transfers to `G` via `Reachable.mono`. -/
protected lemma temporallyConnected_of_TCSpanner (H : Subgraph G) :
    H.IsTCSpanner → G.TemporallyConnectedGraph := by
  intro ⟨h_span, h_tc⟩
  rw [Subgraph.IsSpanning] at h_span
  intro x _ y _
  exact Reachable.mono H.toTemporalGraph_le_self (h_tc x (h_span x) y (h_span y))

/-- Reachability in `H` is preserved by adding vertices (`Subgraph.addVerts`), since
`H ≤ H.addVerts s`. -/
theorem addVerts_reachability {s : Set V} {H : Subgraph G} {x y : V} :
    H.Reachable x y → (H.addVerts s).Reachable x y :=
  reachable_of_le_reachable addVerts_le

/-- Reachability in `H` is preserved by adding an edge (`Subgraph.addEdge`), since
`H ≤ H.addEdge h h₁`. -/
theorem addEdge_reachability {x y : V} {n : ℕ} {H : Subgraph G} [G.IsSymm]
    {h : G.Adj x y n} {h₁ : x ∈ H.verts ∧ y ∈ H.verts} {a b : V} :
    H.Reachable a b → (H.addEdge h h₁).Reachable a b :=
  reachable_of_le_reachable addEdge_le

/-- Reachability in `H.deleteVerts s` implies reachability in `H`, since `H.deleteVerts s ≤ H`. -/
theorem deleteVerts_reachability {s : Set V} {H : Subgraph G} {x y : V} :
    (H.deleteVerts s).Reachable x y → H.Reachable x y :=
  reachable_of_le_reachable deleteVerts_le

/-- The whole graph `⊤ : Subgraph G` is a spanner of itself: it is spanning and trivially
preserves reachability. -/
lemma top_isSpanner : (⊤ : Subgraph G).IsSpanner :=
  ⟨top_isSpanning, fun _ _ _ _ h ↦ h⟩

/-- A temporal graph admits a spanner if and only if it is Temporally Connected -/
@[simp]
theorem TCspanner_iff_TC :
    (∃ (H : Subgraph G), H.IsTCSpanner) ↔ G.TemporallyConnectedGraph := by
  unfold Subgraph.IsTCSpanner
  constructor
  · intro ⟨H, h_span, h_tc⟩
    intro x _ y _
    exact Reachable.mono H.toTemporalGraph_le_self (h_tc x (h_span x) y (h_span y))
  · intro h_tc
    refine ⟨⊤, top_isSpanning, ?_⟩
    intro x _ y _
    exact h_tc x (Set.mem_univ _) y (Set.mem_univ _)

end ReachabilityPreservation

end Subgraph
end TemporalGraph
