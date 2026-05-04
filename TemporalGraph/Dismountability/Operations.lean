/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.SubTemporalGraph
import TemporalGraph.Connectivity.SubTemporalGraph

universe u
variable {V : Type u} {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph

namespace SubTemporalGraph

section Dismount

abbrev dismount (H : SubTemporalGraph G) (x : V) := H.deleteVerts {x}

lemma dismount_clique (H : SubTemporalGraph G) (x : V) (h₀ : H.IsClique) :
    (H.dismount x).IsClique := by
  unfold IsClique dismount
  intro ⟨y, hy⟩ ⟨z, hz⟩ hne
  simp only [induce_Verts, Set.mem_diff, Set.mem_singleton_iff] at hy hz
  have hy' : y ∈ H.Verts := hy.1
  have hz' : z ∈ H.Verts := hz.1
  have ⟨n, hadj⟩ := h₀ ⟨y, hy'⟩ ⟨z, hz'⟩ (by grind only)
  use n
  simp only [induce_Adj, Set.mem_diff, hy', Set.mem_singleton_iff, true_and, hz', hadj, and_true]
  exact ⟨hy.2, hz.2⟩

end Dismount

section Mount -- Entièrement Faux!!!!!!!!

def mount {y z : V} {n m : ℕ} (H : SubTemporalGraph G) (x : V)
    (hee : H.EarliestEdge y x n ∧ y ∈ H.Verts)
    (hle : H.LatestEdge z x m ∧ z ∈ H.Verts) :
    G.SubTemporalGraph :=
  have he : G.Adj y x n := hee.left.left.adj_sub
  have he' : G.Adj z x m := hle.left.left.adj_sub
  have hx : x ∈ (H.addVerts {x}).Verts := by simp only [induce_Verts, Set.union_singleton,
    Set.mem_insert_iff, true_or]
  have hy : y ∈ (H.addVerts {x}).Verts ∧ x ∈ (H.addVerts {x}).Verts := by simp only [induce_Verts,
    Set.union_singleton, Set.mem_insert_iff, hee.right, or_true, true_or, and_self]
  have hz : z ∈ (H.addVerts {x}).Verts ∧ x ∈ (H.addVerts {x}).Verts := by simp only [induce_Verts,
    Set.union_singleton, Set.mem_insert_iff, hle.right, or_true, true_or, and_self]
((H.addVerts {x}).addEdge he hy).addEdge he' hz

lemma mount_Verts {H : SubTemporalGraph G} {x y z : V} {n m : ℕ}
    {hee : H.EarliestEdge y x n ∧ y ∈ H.Verts}
    {hle : H.LatestEdge z x m ∧ z ∈ H.Verts} :
    (mount H x hee hle).Verts = H.Verts ∪ {x} := by
  rw [mount, addEdge_verts, addEdge_verts, addVerts_verts]

lemma mount_edge {H : SubTemporalGraph G} {x y z : V} {n m : ℕ}
    {hee : H.EarliestEdge y x n ∧ y ∈ H.Verts}
    {hle : H.LatestEdge z x m ∧ z ∈ H.Verts} :
    (mount H x hee hle).Adj x y n := by
  simp only [mount, addEdge, induce_Verts, Set.union_singleton, induce_Adj, Set.mem_insert_iff,
    true_or, true_and, and_true, and_self, or_true]

lemma mount_edge' {H : SubTemporalGraph G} {x y z : V} {n m : ℕ}
    {hee : H.EarliestEdge y x n ∧ y ∈ H.Verts}
    {hle : H.LatestEdge z x m ∧ z ∈ H.Verts} :
    (mount H x hee hle).Adj z x m := by
  rw [mount]
  apply addEdge_edge

lemma mount_le {H : SubTemporalGraph G} {x y z : V} {n m : ℕ}
    {hee : H.EarliestEdge y x n ∧ y ∈ H.Verts}
    {hle : H.LatestEdge z x m ∧ z ∈ H.Verts} :
    H ≤ H.mount x hee hle := by
  unfold mount
  have h := addVerts_le' H {x}
  have h' := h.trans <| addEdge_le' (H.addVerts {x}) hee.left.left.adj_sub (by simp [hee.right])
  exact le_trans h' addEdge_le

lemma mount_edgeSet {H : SubTemporalGraph G} {x y z : V} {n m : ℕ}
    {hee : H.EarliestEdge y x n ∧ y ∈ H.Verts}
    {hle : H.LatestEdge z x m ∧ z ∈ H.Verts} :
    (H.mount x hee hle).EdgeSet = H.EdgeSet ∪ {⟨s(z,x), m⟩, ⟨s(y,x), n⟩} := by
  simp only [mount, addEdge_edgeSet, addVerts_edgeSet, Set.union_insert, Set.union_singleton]

lemma mount_earliestEdge {H : SubTemporalGraph G} {x y z : V} {n m : ℕ}
    {hee : H.EarliestEdge y x n ∧ y ∈ H.Verts}
    {hle : H.LatestEdge z x m ∧ z ∈ H.Verts} :
    (mount H x hee hle).EarliestEdge y x n := by
  constructor
  · exact mount_le.right hee.1.1
  · intro x' m' hadj
    suffices h : H.adj x' m'

theorem mount_tc {H : SubTemporalGraph G} {y z : V} {n m : ℕ} (H : SubTemporalGraph G) (x : V)
    (hee : H.EarliestEdge y x n ∧ y ∈ H.Verts)
    (hle : H.LatestEdge z x m ∧ z ∈ H.Verts) :
    H.TemporallyConnected → (mount H x hee hle).TemporallyConnected := by
  have hReach : ∀ x' y', H.Reachable x' y' → (mount H x hee hle).Reachable
    ⟨x', by simp [mount_Verts]⟩
    ⟨y', by simp [mount_Verts]⟩
    := reachable_of_subTempGraph_reachable' mount_le
  unfold SubTemporalGraph.TemporallyConnected
  intro hTC
  simp [mount_Verts]
  intro x' hx' y' hy'
  apply hx'.elim
  · intro h ; apply hy'.elim
    <;> conv => rhs ; lhs ; lhs ; rw [h]
    · intro h'
      conv => rhs ; lhs ; rw [h']
      simpa using @SimpleTemporalGraph.self_reachable _ ((mount H x hee hle).coe) ⟨x, _⟩
    · intro h'
      apply reachable_of_earliestEdge <| hee.left
      exact hReach ⟨y, hee.right⟩ ⟨y', h'⟩ <| hTC _ _
  · intro h ; apply hy'.elim
    · intro h'
      conv => rhs ; lhs ; rw [h']
      apply latest_edge_reachability <| LatestEdge_graph_isof_subgraph hle.left mount_edge'
      exact hReach ⟨x', h⟩ ⟨z, hle.right⟩ <| hTC _ _
    · intro h' ; exact hReach ⟨x', h⟩ ⟨y', h'⟩ <| hTC _ _


end Mount


-- section Mount

-- variable {u : V} {H : SubTemporalGraph G}

-- open SubTemporalGraph

-- def Mount {α β : V} {t s : ℕ} (H : SubTemporalGraph G) (u : V)
-- (hee : G.EarliestEdge α u t ∧ α ∈ H.Verts)
-- (hle : G.LatestEdge β u s ∧ β ∈ H.Verts)
-- : G.SubTemporalGraph
-- :=
--   have he : G.Adj α u t := hee.left.left
--   have he' : G.Adj β u s := hle.left.left
--   have hvu : u ∈ (H.addVerts {u}).Verts := by simp
--   have hv : α ∈ (H.addVerts {u}).Verts ∧ u ∈ (H.addVerts {u}).Verts := by simp [hee.right]
--   have hv' : β ∈ (H.addVerts {u}).Verts ∧ u ∈ (H.addVerts {u}).Verts := by simp [hle.right]
-- ((H.addVerts {u}).addEdge he hv).addEdge he' hv'

-- lemma mount_Verts {α β : V} {t s : ℕ}
-- {hee : G.EarliestEdge α u t ∧ α ∈ H.Verts}
-- {hle : G.LatestEdge β u s ∧ β ∈ H.Verts}
-- : (Mount H u hee hle).Verts = H.Verts ∪ {u}
-- := by rw [Mount, addEdge_Verts, addEdge_Verts, addVerts_Verts]

-- lemma mount_edge {α β : V} {t s : ℕ}
-- {hee : G.EarliestEdge α u t ∧ α ∈ H.Verts}
-- {hle : G.LatestEdge β u s ∧ β ∈ H.Verts}
-- : (Mount H u hee hle).Adj α u t
-- := by
--   rw [Mount]
--   have hv : α ∈ (H.addVerts {u}).Verts ∧ u ∈ (H.addVerts {u}).Verts := by simp [hee.right]
--   have h : ((H.addVerts {u}).addEdge hee.left.left hv).Adj α u t := addEdge_edge
--   have hv' : β ∈ (H.addVerts {u}).Verts ∧ u ∈ (H.addVerts {u}).Verts := by simp [hle.right]
--   have h' : ((H.addVerts {u}).addEdge hee.left.left hv)
--     ≤ ((H.addVerts {u}).addEdge hee.left.left hv).addEdge hle.left.left hv'
--     := addEdge_le
--   apply h'.right h

-- lemma mount_edge' {α β : V} {t s : ℕ}
-- {hee : G.EarliestEdge α u t ∧ α ∈ H.Verts}
-- {hle : G.LatestEdge β u s ∧ β ∈ H.Verts}
-- : (Mount H u hee hle).Adj β u s
-- := by
--   rw [Mount]
--   apply addEdge_edge

-- lemma mount_le {α β : V} {t s : ℕ}
-- {hee : G.EarliestEdge α u t ∧ α ∈ H.Verts}
-- {hle : G.LatestEdge β u s ∧ β ∈ H.Verts}
-- : H ≤ Mount H u hee hle
-- := by
--   unfold Mount
--   have h := addVerts_le' H {u}
--   have h' := h.trans <| addEdge_le' (H.addVerts {u}) hee.left.left (by simp [hee.right])
--   exact le_trans h' addEdge_le

-- theorem mount_tc {α β : V} {t s : ℕ} (H : SubTemporalGraph G) (u : V)
-- (hee : G.EarliestEdge α u t ∧ α ∈ H.Verts)
-- (hle : G.LatestEdge β u s ∧ β ∈ H.Verts)
-- : H.TemporallyConnected → (Mount H u hee hle).TemporallyConnected
-- := by
--   have hReach : ∀ x y, H.Reachable x y → (Mount H u hee hle).Reachable
--     ⟨x, by simp [mount_Verts]⟩
--     ⟨y, by simp [mount_Verts]⟩
--     := SubTemporalGraph.subgraph_reachable_is_reachable' mount_le
--   unfold SubTemporalGraph.TemporallyConnected
--   intro hTC
--   simp [mount_Verts]
--   intro x hx y hy
--   apply hx.elim
--   · intro h ; apply hy.elim
--     <;> conv => rhs ; lhs ; lhs ; rw [h]
--     · intro h'
--       conv => rhs ; lhs ; rw [h']
--       simpa using @SimpleTemporalGraph.self_reachable _ ((Mount H u hee hle).coe) ⟨u, _⟩
--     · intro h'
--       apply earliest_edge_reachability <| EarliestEdge_graph_isof_subgraph hee.left mount_edge
--       exact hReach ⟨α, hee.right⟩ ⟨y, h'⟩ <| hTC _ _
--   · intro h ; apply hy.elim
--     · intro h'
--       conv => rhs ; lhs ; rw [h']
--       apply latest_edge_reachability <| LatestEdge_graph_isof_subgraph hle.left mount_edge'
--       exact hReach ⟨x, h⟩ ⟨β, hle.right⟩ <| hTC _ _
--     · intro h' ; exact hReach ⟨x, h⟩ ⟨y, h'⟩ <| hTC _ _

-- end Mount

end SubTemporalGraph

end SimpleTemporalGraph
