/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Connectivity.Basic
import TemporalGraph.Subgraph

/-!
# Subgraph Reachability and Spanners

Extends reachability and connectivity concepts to subgraphs. Defines spanner types:
`IsSpanner` (reachability-preserving), `IsSpannerOf` (one subgraph as spanner of another),
and `IsTCSpanner` (temporally connected spanner).

## Main definitions
* `Reachable` : Reachability within a subgraph
* `IsSpanner` : A spanning subgraph that preserves reachability
* `IsSpannerOf` : One subgraph spanning and preserving reachability in another
* `TemporallyConnected` : All vertex pairs are mutually reachable within a subgraph
* `IsTCSpanner` : A temporally connected spanner

## Main results
* `reachable_of_subgraph_reachable` : Reachability in subgraph implies reachability in parent
* `reachable_of_le_reachable` : Reachability preserved under subgraph inclusion
* `reachable_of_*Edge` : Reachability preservation via earliest/latest edges
* `TCspanner_iff_TC` : Existence of a TC-spanner characterizes temporal connectivity
-/

universe u
variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

namespace Subgraph

section Reachability

@[simp]
def Reachable (H : Subgraph G) (x y : H.verts) : Prop := H.coe.Reachable x y

@[simp]
lemma reachable_iff_toTemporalGraph {H : Subgraph G} {x y : H.verts} :
    H.Reachable x y ↔ H.toTemporalGraph.Reachable x y := by
  unfold Reachable
  constructor
  · intro ⟨n, m, ⟨w⟩⟩
    exact ⟨n, m, ⟨↑w⟩⟩
  · intro ⟨n, m, ⟨w⟩⟩
    exact ⟨n, m, ⟨↑w⟩⟩

end Reachability

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
  H ≤ H' ∧ ∃ heq : H.verts = H'.verts, ∀ u v : H'.verts , H'.Reachable u v →
  H.Reachable ⟨u, by simp only [heq, Subtype.coe_prop]⟩
              ⟨v, by simp only [heq, Subtype.coe_prop]⟩

end Spanners

section TemporalConnectivity

/-- Every vertex can reach every vertex in the `Subgraph`. -/
def TemporallyConnected (H : Subgraph G) : Prop := ∀ x y : H.verts , H.Reachable x y

@[simp]
lemma temporallyConnected_iff {H : Subgraph G} :
    H.TemporallyConnected ↔ H.coe.TemporallyConnected := by
  apply Iff.intro
  · unfold TemporallyConnected
    intro h
    unfold TemporalGraph.TemporallyConnected
    trivial
  · unfold TemporallyConnected
    intro h
    rw [TemporalGraph.TemporallyConnected] at h
    trivial

lemma toTemporalGraph_temporallyConnected_of_spanning_temporallyConnected
    {H : Subgraph G} :
    H.TemporallyConnected ∧ H.IsSpanning → H.toTemporalGraph.TemporallyConnected := by
  unfold TemporallyConnected IsSpanning
  intro h
  unfold TemporalGraph.TemporallyConnected
  have h' := h.left
  intro x y
  simp only [reachable_iff_toTemporalGraph] at h'
  apply h' ⟨x, h.right x⟩ ⟨y, h.right y⟩

/-- The `Subgraph` `H` is a temporally connected spanner of `G`
if it is spanning and it is temporally connected. -/
def IsTCSpanner (H : Subgraph G) : Prop :=
  (H.IsSpanning) ∧ (H.TemporallyConnected)

theorem isTCSpanner_iff_isSpanner_and_TC {H : Subgraph G} :
    H.IsTCSpanner ↔ H.IsSpanner ∧ H.TemporallyConnected := by
  simp only [IsTCSpanner, temporallyConnected_iff, IsSpanner, Reachable, Subtype.forall,
    and_congr_left_iff, iff_self_and]
  intro htc _ x hx y hy _
  exact htc ⟨x, hx⟩ ⟨y, hy⟩

end TemporalConnectivity

section ReachabilityPreservation

lemma reachable_of_subgraph_reachable {H : Subgraph G} :
    ∀ x y : H.verts, H.Reachable x y → G.Reachable ↑x ↑y := by
  intro _ _ h
  rw [Reachable, reachable_iff_nonempty_univ] at h
  have ⟨n, ⟨m, ⟨p, h⟩⟩⟩ := h
  rw [reachable_iff_nonempty_univ]
  exact ⟨n, ⟨m, ⟨p, h⟩⟩⟩

lemma reachable_of_le_reachable {H : Subgraph G} {H' : Subgraph G}
    (h : H ≤ H') :
    ∀ x y : H.verts, H.Reachable x y → H'.Reachable
      ⟨x, Set.mem_of_subset_of_mem h.left x.prop⟩
      ⟨y, Set.mem_of_subset_of_mem h.left y.prop⟩ := by
  intro _ _ ⟨n, m, ⟨p⟩⟩
  exact ⟨n, m, ⟨p.lift_subtempgraph_walk' h⟩⟩

lemma reachable_of_earliestEdge {H : Subgraph G} {x y : H.verts} {n : ℕ}
    [H.IsSymm] (h₀ : H.EarliestEdge x y n) :
    ∀ z : H.verts, H.Reachable x z → H.Reachable y z := by
  intro z h
  exact H.coe.reachable_of_earliestEdge (coe_earliestEdge h₀) z h

lemma reachable_of_extended_earliestEdge {H : Subgraph G} {x y z : H.verts} {n m : ℕ}
    [H.IsSymm]
    (h₀ : H.EarliestEdge x y n)
    (h₁ : H.Adj z y m)
    (h₂ : m ≤ n) :
    ∀ a : H.verts, H.Reachable x a → H.Reachable z a := by
  intro a h
  exact H.coe.reachable_of_extended_earliestEdge (coe_earliestEdge h₀) h₁ h₂ a h

lemma reachable_of_latestEdge {H : Subgraph G} {x y : H.verts} {n : ℕ}
    [H.IsSymm] (h₀ : H.LatestEdge x y n) :
    ∀ z : H.verts, H.Reachable z x → H.Reachable z y := by
  intro z h
  exact H.coe.reachable_of_latestEdge (coe_latestEdge h₀) z h

lemma reachable_of_extended_latestEdge {H : Subgraph G} {x y z : H.verts} {n m : ℕ}
    [H.IsSymm]
    (h₀ : H.LatestEdge x y n)
    (h₁ : H.Adj y z m)
    (h₂ : n ≤ m) :
    ∀ a : H.verts, H.Reachable a x → H.Reachable a z := by
  intro a h
  exact H.coe.reachable_of_extended_latestEdge (coe_latestEdge h₀) h₁ h₂ a h

protected lemma temporallyConnected_of_TCSpanner (H : Subgraph G) :
    H.IsTCSpanner → G.TemporallyConnected := by
  intro ⟨h_span, h_tc⟩
  unfold TemporallyConnected at h_tc
  rw [Subgraph.IsSpanning] at h_span
  rw [TemporalGraph.TemporallyConnected]
  simp only [Reachable, Subtype.forall, h_span, forall_true_left] at h_tc
  intro x y
  let ⟨n, ⟨m, ⟨p⟩⟩⟩ :=  h_tc x y
  exact ⟨n, ⟨m, ⟨p.lift_subtempgraph_walk⟩⟩⟩

theorem addVerts_reachability {s : Set V} {H : Subgraph G} :
    ∀ x y : H.verts, H.Reachable x y → (H.addVerts s).Reachable ⟨x, by simp⟩ ⟨y, by simp⟩ := by
  exact reachable_of_le_reachable addVerts_le

theorem addEdge_reachability {x y : V} {n : ℕ} {H : Subgraph G} [G.IsSymm]
    {h : G.Adj x y n} {h₁ : x ∈ H.verts ∧ y ∈ H.verts} :
    ∀ x y : H.verts, H.Reachable x y → (H.addEdge h h₁).Reachable x y := by
  exact reachable_of_le_reachable addEdge_le

theorem deleteVerts_reachability {s : Set V} {H : Subgraph G} :
    ∀ x y : (H.deleteVerts s).verts, (H.deleteVerts s).Reachable x y → H.Reachable
      ⟨x, by have h := (deleteVerts_le' H s).left ; rw [Set.subset_def] at h ; cases x with
        |mk x hx => exact h x hx⟩
      ⟨y, by have h := (deleteVerts_le' H s).left ; rw [Set.subset_def] at h ; cases y with
        |mk y hy => exact h y hy⟩ := by
  exact reachable_of_le_reachable deleteVerts_le

lemma top_isSpanner : (⊤ : Subgraph G).IsSpanner := by
  dsimp [IsSpanner]
  constructor
  · exact top_isSpanning
  · intro ⟨x, hx⟩ ⟨y, hy⟩ ⟨n, ⟨m, ⟨tw⟩⟩⟩
    cases tw with
    | Empty => apply reachable_of_self
    | Nonempty p => use n, m ; exact ⟨p.lift_toTemporalGraph_walk⟩

/-- A temporal graph admits a spanner if and only if it is Temporally Connected -/
@[simp]
theorem TCspanner_iff_TC :
    (∃ (H : Subgraph G), H.IsTCSpanner) ↔ G.TemporallyConnected := by
  unfold Subgraph.IsTCSpanner
  apply Iff.intro
  · intro ⟨H, ⟨h_span, h_tc⟩⟩
    unfold TemporallyConnected at h_tc
    rw [IsSpanning] at h_span
    rw [TemporalGraph.TemporallyConnected]
    simp only [Reachable, Subtype.forall, h_span, forall_true_left] at h_tc
    intro x y
    let ⟨_, ⟨_, ⟨tw⟩⟩⟩ :=  h_tc x y
    exact ⟨_, ⟨_, ⟨tw.lift_subtempgraph_walk⟩⟩⟩
  · intro h_tc
    have h'_tc : (⊤ : Subgraph G).TemporallyConnected  := by
      have hspanner : (⊤ : Subgraph G).IsSpanner := top_isSpanner
      rw [TemporalGraph.TemporallyConnected] at h_tc
      intro x y
      exact hspanner.right ↑x ↑y <| h_tc x y
    exact ⟨⊤, ⟨top_isSpanning, h'_tc⟩⟩

end ReachabilityPreservation

end Subgraph
end TemporalGraph
