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

## Main results
* `reachable_of_subgraph_reachable` : Reachability in subgraph implies reachability in parent
* `reachable_of_le_reachable` : Reachability preserved under subgraph inclusion
* `TCspanner_iff_TC` : Existence of a TC-spanner characterizes temporal connectivity
-/

universe u
variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

namespace Subgraph

section Spanners

/-- A `Subgraph` is a spanner of it's original graph `G`, if it's spanning and every
vertices as the same Reachability as in `G`. -/
def IsSpanner (H : Subgraph G) : Prop :=
  H.IsSpanning ∧ ∀ x y : H.verts, G.Reachable x y → H.Reachable x y

-- NOTE(refactor): `G.IsSpanner H.coe` doesn't even type-check via dot notation: `IsSpanner` is
-- nested in `TemporalGraph.Subgraph`, and Lean's dot notation does not search nested
-- namespaces for a matching explicit argument (verified independently of the Loopless/Symm
-- rename: `G : TemporalGraph V` has no argument of type `Subgraph G` to dot into). This
-- looks like it wanted the top-level (currently commented-out) `IsSpanner {s : Set V}
-- (G : TemporalGraph V) (G' : TemporalGraph s) : Prop` from `Connectivity/Basic.lean` instead.
-- The statement can't be restated without that design decision, so it's commented out entirely
-- (not just `sorry`-ed) pending review.
-- @[simp]
-- lemma isSpanner_iff_coe {H : Subgraph G} : H.IsSpanner ↔ G.IsSpanner H.coe := by
--   sorry

/-- A `SubTempGraph` `H` is a spanner of another one `H'` if they have the same vertices and
everything reachable in `H'` is also in `H`. -/
def IsSpannerOf (H : Subgraph G) (H' : Subgraph G) : Prop :=
  H ≤ H' ∧ ∃ _ : H.verts = H'.verts, ∀ u v : H'.verts, H'.Reachable u v → H.Reachable u v

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

theorem isTCSpanner_iff_isSpanner_and_TC {H : Subgraph G} :
    H.IsTCSpanner ↔ H.IsSpanner ∧ H.TemporallyConnectedSubgraph := by
  unfold IsTCSpanner IsSpanner
  constructor
  · intro ⟨h_span, h_tc⟩
    exact ⟨⟨h_span, fun x y _ ↦ h_tc x x.prop y y.prop⟩, h_tc⟩
  · intro ⟨⟨h_span, _⟩, h_tc⟩
    exact ⟨h_span, h_tc⟩

end TemporalConnectivity

section ReachabilityPreservation

/-- Reachability in a subgraph implies reachability in the ambient graph. -/
lemma reachable_of_subgraph_reachable {H : Subgraph G} {x y : V} :
    H.Reachable x y → G.Reachable x y :=
  Reachable.mono H.toTemporalGraph_le_self

/-- Reachability is preserved along subgraph inclusion. -/
lemma reachable_of_le_reachable {H H' : Subgraph G} (h : H ≤ H') {x y : V} :
    H.Reachable x y → H'.Reachable x y :=
  Reachable.mono (toTemporalGraph_le h)

lemma toTemporalGraph_temporallyConnected_of_spanning_temporallyConnected
    {H : Subgraph G} :
    H.TemporallyConnectedSubgraph ∧ H.IsSpanning → H.toTemporalGraph.TemporallyConnectedGraph := by
  intro ⟨h_tc, h_span⟩
  intro x _ y _
  exact h_tc x (h_span x) y (h_span y)

protected lemma temporallyConnected_of_TCSpanner (H : Subgraph G) :
    H.IsTCSpanner → G.TemporallyConnectedGraph := by
  intro ⟨h_span, h_tc⟩
  rw [Subgraph.IsSpanning] at h_span
  intro x _ y _
  exact Reachable.mono H.toTemporalGraph_le_self (h_tc x (h_span x) y (h_span y))

theorem addVerts_reachability {s : Set V} {H : Subgraph G} {x y : V} :
    H.Reachable x y → (H.addVerts s).Reachable x y :=
  reachable_of_le_reachable addVerts_le

theorem addEdge_reachability {x y : V} {n : ℕ} {H : Subgraph G} [G.IsSymm]
    {h : G.Adj x y n} {h₁ : x ∈ H.verts ∧ y ∈ H.verts} {a b : V} :
    H.Reachable a b → (H.addEdge h h₁).Reachable a b :=
  reachable_of_le_reachable addEdge_le

theorem deleteVerts_reachability {s : Set V} {H : Subgraph G} {x y : V} :
    (H.deleteVerts s).Reachable x y → H.Reachable x y :=
  reachable_of_le_reachable deleteVerts_le

lemma top_isSpanner : (⊤ : Subgraph G).IsSpanner :=
  ⟨top_isSpanning, fun _ _ h ↦ h⟩

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
