/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Connectivity.Basic
public import TemporalGraph.Subgraph

/-!
# Subgraph Reachability and Spanners

Reachability and temporal connectivity of a subgraph `H` are those of its underlying graph: since
`Subgraph` extends `TemporalGraph V`, `H.Reachable x y` (for `x y : V`) and
`H.TemporallyConnected S` resolve through generalized field notation to the notions of
`H.toTemporalGraph`. `TemporallyConnectedSubgraph` abbreviates `H.TemporallyConnected H.verts`, as
`IsCliqueSubgraph` does for `IsClique`.

Defines spanner types: `IsSpanner` (reachability-preserving), `IsSpannerOf` (one subgraph as
spanner of another), and `IsTCSpanner` (temporally connected spanner).

## Main definitions

* `IsSpanner` : A spanning subgraph that preserves reachability
* `IsSpannerOf` : One subgraph spanning and preserving reachability in another
* `IsTCSpanner` : A temporally connected spanner
* `TemporallyConnectedSubgraph` : abbreviation for `H.TemporallyConnected H.verts`

## Main results

* `reachable_mono` : Reachability preserved under subgraph inclusion
* `isTCSpanner_iff_isSpanner_and_temporallyConnectedSubgraph` : A TC-spanner is a spanner that
  is temporally connected
* `temporallyConnectedGraph_toTemporalGraph_of_isSpanning` : A spanning subgraph
  temporally connected on its vertices is temporally connected as a graph on all of `V`
* `Subgraph.IsTCSpanner.temporallyConnectedGraph` : A TC-spanner of `G` witnesses that `G` is
  temporally connected
* `exists_isTCSpanner_iff_temporallyConnectedGraph` : Existence of a TC-spanner characterizes
  temporal connectivity
* `mem_verts_of_reachable` : A reachable pair of distinct vertices lies in `H`'s own vertex set
* `top_isSpanner` : The whole graph `⊤` is a spanner of itself
* `isSpannerOf_of_le_of_temporallyConnected` : a subgraph of a nontrivial `H` that is temporally
  connected on `H.verts` is a spanner of `H`
* `Reachable.addVerts`, `Reachable.addEdge`, `Reachable.of_deleteVerts` : reachability is
  preserved by these subgraph constructions
* `TemporalWalk.reachableBefore_fromEdgeSet` : a walk whose edges lie in `E` reaches its end, by
  its arrival time, in `Subgraph.fromEdgeSet G E`
* `ReachableWithin.step_fromEdgeSet` : extend a window-bounded walk of `Subgraph.fromEdgeSet G E`
  by the arc of a subgraph `H` whose edge lies in `E`
-/

@[expose] public section

universe u
variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

namespace Subgraph

section Spanners

/-- `H` is a spanner of `G`: it is spanning (`H.IsSpanning`: all of `V` are vertices of `H`) and
every pair of vertices reachable in `G` is reachable in `H`. Unlike `IsSpanning`, this constrains
the arcs of `H`. -/
def IsSpanner (H : Subgraph G) : Prop :=
  H.IsSpanning ∧ ∀ x ∈ H.verts, ∀ y ∈ H.verts, G.Reachable x y → H.Reachable x y

/-- `H` is a spanner of the subgraph `H'`: `H ≤ H'`, they have the same vertices, and every pair
of vertices reachable in `H'` is reachable in `H`. -/
def IsSpannerOf (H : Subgraph G) (H' : Subgraph G) : Prop :=
  H ≤ H' ∧ H.verts = H'.verts ∧ ∀ x ∈ H'.verts, ∀ y ∈ H'.verts, H'.Reachable x y → H.Reachable x y

end Spanners

section TemporalConnectivity

/-- `H` is temporally connected on its own vertex set. Shorthand for
`H.TemporallyConnected H.verts`. -/
abbrev TemporallyConnectedSubgraph (H : Subgraph G) : Prop :=
  H.TemporallyConnected H.verts

/-- `H` is a temporally connected spanner of `G`: it is spanning (`H.IsSpanning`) and temporally
connected on its vertices, hence on all of `V`. -/
def IsTCSpanner (H : Subgraph G) : Prop :=
  H.IsSpanning ∧ H.TemporallyConnectedSubgraph

/-- `H.IsTCSpanner` is equivalent to `H.IsSpanner ∧ H.TemporallyConnectedSubgraph`: once `H` is
temporally connected on its own vertices, the spanner condition holds vacuously (`H.Reachable x y`
already holds, regardless of `G.Reachable x y`). -/
theorem isTCSpanner_iff_isSpanner_and_temporallyConnectedSubgraph {H : Subgraph G} :
    H.IsTCSpanner ↔ H.IsSpanner ∧ H.TemporallyConnectedSubgraph := by
  unfold IsTCSpanner IsSpanner
  exact ⟨fun ⟨h₀, h₁⟩ ↦ ⟨⟨h₀, fun x hx y hy _ ↦ h₁ x hx y hy⟩, h₁⟩, fun ⟨⟨h₀, _⟩, h₁⟩ ↦ ⟨h₀, h₁⟩⟩

end TemporalConnectivity

section ReachabilityPreservation

/-- A reachable pair of distinct vertices lies in `H`'s own vertex set: a walk witnessing the
reachability is nonempty (`x ≠ y` rules out `TemporalWalk.nil`), and its first and last arcs
give each endpoint's membership. -/
lemma mem_verts_of_reachable {H : Subgraph G} {x y : V} (h₀ : H.Reachable x y) (h₁ : x ≠ y) :
    x ∈ H.verts ∧ y ∈ H.verts := by
  obtain ⟨n, m, ⟨w⟩⟩ := h₀
  cases w with
  | nil => exact absurd rfl h₁
  | ofNonempty p =>
    obtain ⟨z, j, hz⟩ := p.exists_adj_fst
    obtain ⟨z', j', hz'⟩ := p.exists_adj_snd
    exact ⟨H.edge_vert hz, H.edge_vert' hz'⟩

/-- Reachability is preserved along subgraph inclusion. -/
lemma reachable_mono {H H' : Subgraph G} (h : H ≤ H') {x y : V} :
    H.Reachable x y → H'.Reachable x y :=
  Reachable.mono (toTemporalGraph_le h)

@[deprecated (since := "2026-10-29")]
alias reachable_of_le_reachable := reachable_mono

/-- If `H` is spanning and temporally connected on its own vertices, then `H`'s own adjacency
(`H.toTemporalGraph`) is temporally connected on all of `V`: spanning turns the quantification
over `H.verts` into one over `Set.univ`. -/
lemma temporallyConnectedGraph_toTemporalGraph_of_isSpanning {H : Subgraph G}
    (h₀ : H.TemporallyConnectedSubgraph) (h₁ : H.IsSpanning) :
    H.toTemporalGraph.TemporallyConnectedGraph :=
  fun x _ y _ ↦ h₀ x (h₁ x) y (h₁ y)

/-- A TC-spanner of `G` witnesses that `G` itself is temporally connected: reachability in `H`
transfers to `G` via `Reachable.mono`. -/
lemma IsTCSpanner.temporallyConnectedGraph {H : Subgraph G} :
    H.IsTCSpanner → G.TemporallyConnectedGraph := by
  intro ⟨h_span, h_tc⟩ x _ y _
  exact Reachable.mono H.toTemporalGraph_le_self (h_tc x (h_span x) y (h_span y))

/-- Reachability in `H` is preserved by adding vertices (`Subgraph.addVerts`), since
`H ≤ H.addVerts s`. -/
theorem _root_.TemporalGraph.Reachable.addVerts {s : Set V} {H : Subgraph G} {x y : V} :
    H.Reachable x y → (H.addVerts s).Reachable x y :=
  reachable_mono addVerts_le

/-- Reachability in `H` is preserved by adding an edge (`Subgraph.addEdge`), since
`H ≤ H.addEdge h h₁`. -/
theorem _root_.TemporalGraph.Reachable.addEdge {x y : V} {n : ℕ} {H : Subgraph G} [G.IsSymm]
    {h : G.Adj x y n} {h₁ : x ∈ H.verts ∧ y ∈ H.verts} {a b : V} :
    H.Reachable a b → (H.addEdge h h₁).Reachable a b :=
  reachable_mono addEdge_le

/-- Reachability in `H.deleteVerts s` implies reachability in `H`, since `H.deleteVerts s ≤ H`. -/
theorem _root_.TemporalGraph.Reachable.of_deleteVerts {s : Set V} {H : Subgraph G} {x y : V} :
    (H.deleteVerts s).Reachable x y → H.Reachable x y :=
  reachable_mono deleteVerts_le

/-- The whole graph `⊤ : Subgraph G` is a spanner of itself: it is spanning and trivially
preserves reachability. -/
lemma top_isSpanner : (⊤ : Subgraph G).IsSpanner :=
  ⟨isSpanning_top, fun _ _ _ _ h ↦ h⟩

/-- A temporal graph has a temporally connected spanner if and only if it is temporally
connected. -/
theorem exists_isTCSpanner_iff_temporallyConnectedGraph :
    (∃ (H : Subgraph G), H.IsTCSpanner) ↔ G.TemporallyConnectedGraph := by
  unfold Subgraph.IsTCSpanner
  constructor
  · rintro ⟨H, hH⟩
    exact IsTCSpanner.temporallyConnectedGraph hH
  · -- the whole graph `⊤` is a temporally connected spanner
    intro h_tc
    refine ⟨⊤, isSpanning_top, ?_⟩
    intro x _ y _
    exact h_tc x (Set.mem_univ _) y (Set.mem_univ _)

/-- A subgraph `K ≤ H` that is temporally connected on the vertices of a nontrivial `H` is a
spanner of `H`: it has all the vertices of `H`, each being reached from another one, and every
pair of vertices of `H` is reachable in `K`. -/
theorem isSpannerOf_of_le_of_temporallyConnected {K H : Subgraph G} [Nontrivial H.verts]
    (h₀ : K ≤ H) (h₁ : K.TemporallyConnected H.verts) : K.IsSpannerOf H := by
  refine ⟨h₀, Set.Subset.antisymm h₀.left fun x hx ↦ ?_, fun x hx y hy _ ↦ h₁ x hx y hy⟩
  -- `x` reaches some other vertex `y` of `H`, so `x` is a vertex of `K`
  obtain ⟨y, hy, hxy⟩ := (Set.nontrivial_coe_sort.mp ‹Nontrivial H.verts›).exists_ne x
  exact (mem_verts_of_reachable (h₁ x hx y hy) hxy.symm).1

end ReachabilityPreservation

end Subgraph

/-- A walk of a subgraph `H` whose edges all lie in `E` shows that its end is reachable from its
start in `Subgraph.fromEdgeSet G E`, arriving by the walk's arrival time. -/
theorem TemporalWalk.reachableBefore_fromEdgeSet {H : Subgraph G} {x y : V} {n m : ℕ}
    (p : H.toTemporalGraph.TemporalWalk x n y m) {E : Set (Sym2 V × ℕ)}
    (h₀ : ∀ e ∈ p.edges, e ∈ E) : (Subgraph.fromEdgeSet G E).ReachableBefore x y m := by
  refine ⟨n, m, Nat.zero_le _, le_rfl, ⟨p.transfer _ fun a ha ↦ ?_⟩⟩
  -- the arc `a` of `p` is an arc of `H`, hence of `G`, and its edge lies in `E`
  have hE : (s(a.1, a.2.1), a.2.2) ∈ E := h₀ _ (List.mem_map.2 ⟨a, ha, rfl⟩)
  exact Subgraph.adj_fromEdgeSet hE (H.adj_sub (p.adj_of_mem_arcs a ha).1)

/-- Extend a window-bounded walk of `Subgraph.fromEdgeSet G E` by the arc `y → z` of a subgraph
`H` of `G`, at time `k`, when the edge `{y, z}` of `E` is at this time. -/
theorem ReachableWithin.step_fromEdgeSet {H : Subgraph G} {E : Set (Sym2 V × ℕ)}
    {x y z : V} {a b k : ℕ} (h₀ : (Subgraph.fromEdgeSet G E).ReachableWithin x y a b)
    (h₁ : H.Adj y z k) (h₂ : (s(y, z), k) ∈ E) (h₃ : b ≤ k) :
    (Subgraph.fromEdgeSet G E).ReachableWithin x z a k :=
  h₀.step ⟨⟨_, h₂⟩, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _, rfl, H.adj_sub h₁⟩ h₃

end TemporalGraph
