/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Subgraph.Basic

/-!
# Subgraph operations

Adding an edge to a subgraph, the transfer of earliest and latest edges between a subgraph and its
ambient graph, and the neighbor set of a subgraph.

## Main definitions

* `Subgraph.addArc`, `Subgraph.addEdge` : adding one orientation of an edge (no symmetry needed),
  resp. both orientations (needs `[G.IsSymm]`).

## Main results

* `addArc_le`, `addEdge_le`, `addArc_le_addEdge`, and the instance `addEdge_isSymm`.
* Earliest and latest edges: `top_earliestEdge`, `top_latestEdge`, `earliestEdge_lt_of_proper`,
  the `coe_*`/`*_of_coe`/`*_of_graph_*`/`*_of_ge` transfer lemmas.
* `top_neighborSet`, `neighborSet_subset_verts`.
-/

@[expose] public section

universe u

namespace TemporalGraph

namespace Subgraph

variable {V : Type u} {G : TemporalGraph V}

section AddEdge

variable {x y : V} {n : ℕ}

/-- Add the single, oriented edge `(x, y)` at time `n`. Needs no symmetry whatsoever: use
`addEdge` to add both orientations at once. -/
def addArc (H : Subgraph G) (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    Subgraph G where
  verts := H.verts
  Adj x' y' n' := H.Adj x' y' n' ∨ (x' = x ∧ y' = y ∧ n' = n)
  edge_vert := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩)
    · exact H.edge_vert hadj
    · exact h₁.left
  edge_vert' := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩)
    · exact H.edge_vert' hadj
    · exact h₁.right
  adj_sub := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩)
    · exact H.adj_sub hadj
    · exact h

/-- Add both orientations of the edge between `x` and `y` at time `n`. Unlike `addArc` this
needs `G.IsSymm`, to see the reversed orientation back in `G`. -/
def addEdge (H : Subgraph G) [G.IsSymm] (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    Subgraph G where
  verts := H.verts
  Adj x' y' n' := H.Adj x' y' n' ∨ (x' = x ∧ y' = y ∧ n' = n) ∨ (y' = x ∧ x' = y ∧ n' = n)
  edge_vert := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact H.edge_vert hadj
    · exact h₁.left
    · exact h₁.right
  edge_vert' := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact H.edge_vert' hadj
    · exact h₁.right
    · exact h₁.left
  adj_sub := by
    rintro _ _ _ (hadj | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · exact H.adj_sub hadj
    · exact h
    · exact h.symm

variable {H : Subgraph G} {h : G.Adj x y n}
  {h₁ : x ∈ H.verts ∧ y ∈ H.verts}

/-- `H` is below `H.addArc h h₁`, the subgraph obtained by adding the arc `(x, y)` at time `n`. -/
@[simp]
theorem addArc_le : H ≤ addArc H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

/-- The arc `(x, y)` at time `n` just added is indeed an adjacency of `H.addArc h h₁`. -/
@[simp]
theorem addArc_arc : (addArc H h h₁).Adj x y n :=
  Or.inr ⟨rfl, rfl, rfl⟩

/-- Adding an arc does not change the vertex set. -/
@[simp, grind =]
theorem addArc_verts : (addArc H h h₁).verts = H.verts := rfl

/-- `H` is below `H.addEdge h h₁`, the subgraph obtained by adding both orientations of the edge
between `x` and `y` at time `n`. -/
@[simp]
theorem addEdge_le [G.IsSymm] : H ≤ addEdge H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

/-- The orientation `(x, y)` at time `n` of the edge just added is an adjacency of
`H.addEdge h h₁`. -/
@[simp]
theorem addEdge_edge [G.IsSymm] : (addEdge H h h₁).Adj x y n :=
  Or.inr <| Or.inl ⟨rfl, rfl, rfl⟩

/-- Adding an edge does not change the vertex set. -/
@[simp, grind =]
theorem addEdge_verts [G.IsSymm] : (addEdge H h h₁).verts = H.verts := rfl

/-- The oriented `addArc` is the weaker of the two constructions. -/
theorem addArc_le_addEdge [G.IsSymm] : addArc H h h₁ ≤ addEdge H h h₁ :=
  ⟨subset_rfl, fun hadj ↦ hadj.elim Or.inl (fun h' ↦ Or.inr <| Or.inl h')⟩

instance addEdge_isSymm (H : Subgraph G) [G.IsSymm] [H.IsSymm]
    (h : G.Adj x y n) (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    (addEdge H h h₁).IsSymm := by
  refine IsSymm.of_adj ?_
  intro m _ _ hadj
  -- the old arcs are reversed by symmetry of `H`; the two new orientations are swapped
  rcases hadj with hadj | hxy | hyx
  · exact Or.inl (TemporalGraph.adj_symm hadj)
  · exact Or.inr (Or.inr hxy)
  · exact Or.inr (Or.inl hyx)

end AddEdge

section EdgeProps

variable {x y : V} {n : ℕ}

/-- `(x, y, n)` is `⊤ : Subgraph G`'s earliest edge at `x` iff it is `G`'s. -/
lemma top_earliestEdge :
    (⊤ : Subgraph G).EarliestEdge x y n ↔ G.EarliestEdge x y n := by
  simp [TemporalGraph.EarliestEdge, top_adj]

/-- `(x, y, n)` is `⊤ : Subgraph G`'s latest edge at `x` iff it is `G`'s. -/
lemma top_latestEdge :
    (⊤ : Subgraph G).LatestEdge x y n ↔ G.LatestEdge x y n := by
  simp [TemporalGraph.LatestEdge, top_adj]

/-- In a proper subgraph, any adjacency out of `x` to a vertex other than its earliest neighbor
`y` happens strictly after the earliest edge `(x, y, n)`. -/
lemma earliestEdge_lt_of_proper {H : Subgraph G} {z : V} {m : ℕ}
    (h₀ : H.IsProper)
    (h₁ : H.EarliestEdge x y n)
    (h₂ : H.Adj x z m)
    (h₄ : y ≠ z) :
    n < m := by
  refine (h₁.right _ _ h₂).lt_of_ne fun h ↦ h₄ ?_
  -- if the times coincide, properness forces `y = z`
  exact h₀ h₁.left (h ▸ h₂)

/-- `y` is `⊤ : Subgraph G`'s earliest neighbor of `x` iff it is `G`'s. -/
lemma top_earliestNeighbor :
    (⊤ : Subgraph G).EarliestNeighbor x y ↔ G.EarliestNeighbor x y := by
  simp [TemporalGraph.EarliestNeighbor, top_earliestEdge]

/-- `y` is `⊤ : Subgraph G`'s latest neighbor of `x` iff it is `G`'s. -/
lemma top_latestNeighbor :
    (⊤ : Subgraph G).LatestNeighbor x y ↔ G.LatestNeighbor x y := by
  simp [TemporalGraph.LatestNeighbor, top_latestEdge]

/-- If `(x, y, n)` is `G`'s earliest edge at `x` and also an adjacency of `H`, it is the earliest
edge at `x` in the subtype view `H.coe`. -/
lemma coe_earliestEdge_of_graph_earliestEdge {H : Subgraph G}
    (h₀ : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.EarliestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ n := by
  refine ⟨h₁, fun z m hadj ↦ ?_⟩
  -- the extremality of `(x, y, n)` in `G` transfers to the subtype view
  exact h₀.right z m (H.adj_sub hadj)

/-- If `(x, y, n)` is `G`'s latest edge at `x` and also an adjacency of `H`, it is the latest
edge at `x` in the subtype view `H.coe`. -/
lemma coe_latestEdge_of_graph_latestEdge {H : Subgraph G}
    (h₀ : G.LatestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.LatestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ n := by
  refine ⟨h₁, fun z m hadj ↦ ?_⟩
  -- the extremality of `(x, y, n)` in `G` transfers to the subtype view
  exact h₀.right z m (H.adj_sub hadj)

/-- An earliest edge of `H` is an earliest edge of its subtype view `H.coe`. -/
lemma coe_earliestEdge {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.EarliestEdge x y n) :
    H.coe.EarliestEdge x y n :=
  ⟨Adj.coe h₀.left, fun _ _ h ↦ h₀.right _ _ h⟩

/-- An earliest edge of the subtype view `H.coe` is an earliest edge of `H`. -/
lemma earliestEdge_of_coe {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.coe.EarliestEdge x y n) :
    H.EarliestEdge x y n :=
  ⟨h₀.left, fun _ _ h ↦ h₀.right _ _ (Adj.coe h)⟩

/-- If `(x, y, n)` is `G`'s earliest edge at `x` and also an adjacency of `H`, it is `H`'s
earliest edge at `x`. -/
lemma earliestEdge_of_graph_earliestEdge {H : Subgraph G}
    (h₀ : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.EarliestEdge x y n :=
  ⟨h₁, fun _ _ h ↦ h₀.right _ _ (H.adj_sub h)⟩

/-- If `H'`'s earliest edge at `x` is already an adjacency of the smaller `H ≤ H'`, it is `H`'s
earliest edge at `x` too. -/
lemma earliestEdge_of_le {H H' : Subgraph G} (h₀ : H ≤ H') (h₁ : H'.EarliestEdge x y n)
    (h₂ : H.Adj x y n) :
    H.EarliestEdge x y n :=
  ⟨h₂, fun _ _ h ↦ h₁.right _ _ (h₀.right h)⟩

/-- A latest edge of `H` is a latest edge of its subtype view `H.coe`. -/
lemma coe_latestEdge {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.LatestEdge x y n) :
    H.coe.LatestEdge x y n :=
  ⟨Adj.coe h₀.left, fun _ _ h ↦ h₀.right _ _ h⟩

/-- A latest edge of the subtype view `H.coe` is a latest edge of `H`. -/
lemma latestEdge_of_coe {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.coe.LatestEdge x y n) :
    H.LatestEdge x y n :=
  ⟨h₀.left, fun _ _ h ↦ h₀.right _ _ (Adj.coe h)⟩

/-- If `(x, y, n)` is `G`'s latest edge at `x` and also an adjacency of `H`, it is `H`'s latest
edge at `x`. -/
lemma latestEdge_of_graph_latestEdge {H : Subgraph G}
    (h₀ : G.LatestEdge x y n) (h₁ : H.Adj x y n) :
    H.LatestEdge x y n :=
  ⟨h₁, fun _ _ h ↦ h₀.right _ _ (H.adj_sub h)⟩

/-- If `H'`'s latest edge at `x` is already an adjacency of the smaller `H ≤ H'`, it is `H`'s
latest edge at `x` too. -/
lemma latestEdge_of_le {H H' : Subgraph G} (h₀ : H ≤ H') (h₁ : H'.LatestEdge x y n)
    (h₂ : H.Adj x y n) :
    H.LatestEdge x y n :=
  ⟨h₂, fun _ _ h ↦ h₁.right _ _ (h₀.right h)⟩

end EdgeProps

section NeighborHoodSet

/-- The neighbor set of `x` in `⊤ : Subgraph G` is `x`'s neighbor set in `G`. -/
theorem top_neighborSet (x : V) :
    (⊤ : G.Subgraph).neighborSet x = G.neighborSet x := rfl

/-- The neighbor set of any vertex is contained in `H.verts`. -/
theorem neighborSet_subset_verts (H : Subgraph G) (x : V) :
    H.neighborSet x ⊆ H.verts := by
  intro _ h
  obtain ⟨_, h⟩ := (H.mem_neighborSet _ _).mp h
  exact H.edge_vert' h

end NeighborHoodSet

end Subgraph

end TemporalGraph
