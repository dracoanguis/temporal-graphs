/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Connectivity.Basic
import TemporalGraph.SubTemporalGraph
import TemporalGraph.Connectivity.SubTemporalGraph

universe u
variable {V : Type u} {G : LooplessTemporalGraph V}

namespace SimpleTemporalGraph

theorem mountable_construct' {u v w : V} {t₁ t₂ : ℕ}
(G : LooplessTemporalGraph V) (G' : SubTemporalGraph G)
(h : G.EarliestEdge v u t₁ ∧ G.LatestEdge w u t₂)
(h' : G'.Verts = {α:V| α≠u} ∧ G'.TemporallyConnected) : G.TemporallyConnected
:= by
  rw [SimpleTemporalGraph.TemporallyConnected]
  rcases h with ⟨hee, hle⟩
  rw [SimpleTemporalGraph.EarliestEdge] at hee
  rw [SimpleTemporalGraph.LatestEdge] at hle
  rcases h' with ⟨hnu, htc⟩
  rw [SubTemporalGraph.TemporallyConnected] at htc
  have hvin : v∈G'.Verts := by rw [hnu] ; exact hee.left.ne
  have hwin : w∈G'.Verts := by rw [hnu] ; exact hle.left.ne
  have htc' := fun x y : G'.Verts ↦ G'.subgraph_reachable_is_reachable x y (htc x y)
  have hfur := fun x : G'.Verts ↦ earliest_edge_reachability hee x (htc' ⟨v, hvin⟩ x)
  have htur := fun x : G'.Verts ↦ latest_edge_reachability hle x (htc' x ⟨w, hwin⟩)
  have huu := G.self_reachable u
  intro x y
  by_cases hcase : x=u
  · rw [hcase]
    by_cases hcase' : y=u
    · rw [hcase']
      exact huu
    · exact hfur ⟨y, by rwa [hnu]⟩
  · by_cases hcase' : y=u
    · rw [hcase']
      exact htur ⟨x, by rwa [hnu]⟩
    · exact htc' ⟨x, by rwa [hnu]⟩ ⟨y, by rwa [hnu]⟩

def V_minus (G : LooplessTemporalGraph V) : Set V := {u | ∃ α, G.EarliestNeighbor α u}

def V_plus (G : LooplessTemporalGraph V) : Set V := {u | ∃ β, G.LatestNeighbor β u}

def V_zero (G : LooplessTemporalGraph V) : Set V := {u | u ∉ G.V_minus ∧ u ∉ G.V_plus}

namespace SubTemporalGraph

section Mountable

section Definition

variable (u : V) (H : SubTemporalGraph G)

def VMinus : Set V
:= {u | ∃ α, G.EarliestNeighbor α u ∧ u ∉ H.Verts ∧ α ∈ H.Verts}

def VPlus : Set V
:= {u | ∃ β, G.LatestNeighbor β u ∧ u ∉ H.Verts ∧ β ∈ H.Verts}

def VZero : Set V := {u | u ∉ H.VMinus ∧ u ∉ H.VPlus}

def MountableMinusOn := ∃ α, G.EarliestNeighbor α u ∧ u ∉ H.Verts ∧ α ∈ H.Verts

lemma vMinus_iff_MountableMinusOn
: u ∈ H.VMinus ↔ MountableMinusOn u H
:= by
  constructor
  <;> intro ⟨α, hen, hu, hα⟩
  <;> exact ⟨α, hen, hu, hα⟩

-- Is it useless?
def MountableMinus := ∃ u, MountableMinusOn u H

def MountablePlusOn := ∃ β, G.LatestNeighbor β u ∧ u ∉ H.Verts ∧ β ∈ H.Verts

lemma vPlus_iff_MountablePlusOn
: u ∈ H.VPlus ↔ MountablePlusOn u H
:= by
  constructor
  <;> intro ⟨β, hln, hu, hβ⟩
  <;> exact ⟨β, hln, hu, hβ⟩

-- useless?
def MountablePlus := ∃ u, MountablePlusOn u H

def MountableOn := MountableMinusOn u H ∧ MountablePlusOn u H

def Mountable := ∃ u, MountableMinusOn u H ∧ MountablePlusOn u H

end Definition

variable {u : V} {H : SubTemporalGraph G}

@[simp]
lemma mountableOn_imp_mountable : MountableOn u H → Mountable H
:= by intro ⟨hₘ, hₚ⟩ ; exact ⟨u, hₘ, hₚ⟩

theorem vMinus_inter_VPlus_iff_mountableOn
: u ∈ (H.VMinus ∩ H.VPlus) ↔ MountableOn u H
:= by
  constructor
  <;> intro ⟨hm, hp⟩
  <;> exact ⟨hm, hp⟩

theorem not_mountableOn_imp_partition
: ¬Mountable H → ∀ a, ∃! b ∈ ({H.VZero, H.VMinus, H.VPlus, H.Verts} : Set (Set V)), a ∈ b
:= by
  intro h a
  rw [Mountable] at h
  push_neg at h
  conv at h => rhs ; lhs ; rw [←vMinus_iff_MountableMinusOn]
  conv at h => rhs ; rhs ; rw [←vPlus_iff_MountablePlusOn]
  rw [ExistsUnique]
  by_contra h'
  push_neg at h'


section Mount

def Mount {α β : V} {t s : ℕ} (H : SubTemporalGraph G) (u : V)
(hee : G.EarliestEdge α u t ∧ α ∈ H.Verts)
(hle : G.LatestEdge β u s ∧ β ∈ H.Verts)
: G.SubTemporalGraph
:=
  have he : G.Adj α u t := hee.left.left
  have he' : G.Adj β u s := hle.left.left
  have hvu : u ∈ (H.addVerts {u}).Verts := by simp
  have hv : α ∈ (H.addVerts {u}).Verts ∧ u ∈ (H.addVerts {u}).Verts := by simp [hee.right]
  have hv' : β ∈ (H.addVerts {u}).Verts ∧ u ∈ (H.addVerts {u}).Verts := by simp [hle.right]
((H.addVerts {u}).addEdge he hv).addEdge he' hv'

lemma mount_Verts {α β : V} {t s : ℕ}
{hee : G.EarliestEdge α u t ∧ α ∈ H.Verts}
{hle : G.LatestEdge β u s ∧ β ∈ H.Verts}
: (Mount H u hee hle).Verts = H.Verts ∪ {u}
:= by rw [Mount, addEdge_Verts, addEdge_Verts, addVerts_Verts]

lemma mount_edge {α β : V} {t s : ℕ}
{hee : G.EarliestEdge α u t ∧ α ∈ H.Verts}
{hle : G.LatestEdge β u s ∧ β ∈ H.Verts}
: (Mount H u hee hle).Adj α u t
:= by
  rw [Mount]
  have hv : α ∈ (H.addVerts {u}).Verts ∧ u ∈ (H.addVerts {u}).Verts := by simp [hee.right]
  have h : ((H.addVerts {u}).addEdge hee.left.left hv).Adj α u t := addEdge_edge
  have hv' : β ∈ (H.addVerts {u}).Verts ∧ u ∈ (H.addVerts {u}).Verts := by simp [hle.right]
  have h' : ((H.addVerts {u}).addEdge hee.left.left hv)
    ≤ ((H.addVerts {u}).addEdge hee.left.left hv).addEdge hle.left.left hv'
    := addEdge_le
  apply h'.right h

lemma mount_edge' {α β : V} {t s : ℕ}
{hee : G.EarliestEdge α u t ∧ α ∈ H.Verts}
{hle : G.LatestEdge β u s ∧ β ∈ H.Verts}
: (Mount H u hee hle).Adj β u s
:= by
  rw [Mount]
  apply addEdge_edge

lemma mount_le {α β : V} {t s : ℕ}
{hee : G.EarliestEdge α u t ∧ α ∈ H.Verts}
{hle : G.LatestEdge β u s ∧ β ∈ H.Verts}
: H ≤ Mount H u hee hle
:= by
  unfold Mount
  have h := addVerts_le' H {u}
  have h' := h.trans <| addEdge_le' (H.addVerts {u}) hee.left.left (by simp [hee.right])
  exact le_trans h' addEdge_le

theorem mount_tc {α β : V} {t s : ℕ} (H : SubTemporalGraph G) (u : V)
(hee : G.EarliestEdge α u t ∧ α ∈ H.Verts)
(hle : G.LatestEdge β u s ∧ β ∈ H.Verts)
: H.TemporallyConnected → (Mount H u hee hle).TemporallyConnected
:= by
  have hReach : ∀ x y, H.Reachable x y → (Mount H u hee hle).Reachable
    ⟨x, by simp [mount_Verts]⟩
    ⟨y, by simp [mount_Verts]⟩
    := SubTemporalGraph.subgraph_reachable_is_reachable' mount_le
  unfold SubTemporalGraph.TemporallyConnected
  intro hTC
  simp [mount_Verts]
  intro x hx y hy
  apply hx.elim
  · intro h ; apply hy.elim
    <;> conv => rhs ; lhs ; lhs ; rw [h]
    · intro h'
      conv => rhs ; lhs ; rw [h']
      simpa using @SimpleTemporalGraph.self_reachable _ ((Mount H u hee hle).coe) ⟨u, _⟩
    · intro h'
      apply earliest_edge_reachability <| EarliestEdge_graph_isof_subgraph hee.left mount_edge
      exact hReach ⟨α, hee.right⟩ ⟨y, h'⟩ <| hTC _ _
  · intro h ; apply hy.elim
    · intro h'
      conv => rhs ; lhs ; rw [h']
      apply latest_edge_reachability <| LatestEdge_graph_isof_subgraph hle.left mount_edge'
      exact hReach ⟨x, h⟩ ⟨β, hle.right⟩ <| hTC _ _
    · intro h' ; exact hReach ⟨x, h⟩ ⟨y, h'⟩ <| hTC _ _

end Mount

end Mountable

section Mountable2

section Definition

variable (u : V) (H : SubTemporalGraph G)

def Mountable2MinusOn
:= MountableMinusOn u H
  ∨ ∃ α α' t t', G.EarliestEdge α α' t ∧ G.Adj α u t' ∧ t' ≤ t
    ∧ {α, α'} ⊆ H.Verts ∧ u ∉ H.Verts

def Mountable2PlusOn
:= MountablePlusOn u H
  ∨ ∃ β β' t t', G.LatestEdge β β' t ∧ G.Adj β' u t' ∧ t ≤ t'
    ∧ {β, β'} ⊆ H.Verts ∧ u ∉ H.Verts

def Mountable2On := Mountable2MinusOn u H ∧ Mountable2PlusOn u H

def Mountable2 := ∃ u, Mountable2On u H

end Definition

variable {u : V} {H : SubTemporalGraph G}

lemma mountableMinusOn_imp_Mountable2MinusOn
: MountableMinusOn u H → Mountable2MinusOn u H
:= by intro h ; exact Or.inl h

lemma MountablePlusOn_imp_Mountable2PlusOn
: MountablePlusOn u H → Mountable2PlusOn u H
:= by intro h ; exact Or.inl h

lemma MountableOn_imp_Mountable2On
: MountableOn u H → Mountable2On u H
:= by
  intro ⟨h, h'⟩
  exact ⟨mountableMinusOn_imp_Mountable2MinusOn h, MountablePlusOn_imp_Mountable2PlusOn h'⟩

theorem vZero_imp_Mountable2
: u ∈ H.VZero ∧ H.TemporallyConnected → Mountable2On u (H.deleteVerts {u})
:= by
  intro ⟨h, h'⟩


end Mountable2

end SubTemporalGraph

end SimpleTemporalGraph
