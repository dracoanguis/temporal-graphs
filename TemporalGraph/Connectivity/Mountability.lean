import TemporalGraph.Connectivity.Basic

import TemporalGraph.SubTempGraph
import TemporalGraph.Connectivity.SubTempGraph

universe u
variable {V : Type u} {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph

theorem mountable_construct' {u v w : V} {t₁ t₂ : ℕ}
(G : SimpleTemporalGraph V) (G' : SubTempGraph G)
(h : G.EarliestEdge v u t₁ ∧ G.LatestEdge w u t₂)
(h' : G'.verts = {α:V| α≠u} ∧ G'.TemporallyConnected) : G.TemporallyConnected
:= by
  rw [SimpleTemporalGraph.TemporallyConnected]
  rcases h with ⟨hee, hle⟩
  rw [SimpleTemporalGraph.EarliestEdge] at hee
  rw [SimpleTemporalGraph.LatestEdge] at hle
  rcases h' with ⟨hnu, htc⟩
  rw [SubTempGraph.TemporallyConnected] at htc
  have hvin : v∈G'.verts := by rw [hnu] ; exact hee.left.ne
  have hwin : w∈G'.verts := by rw [hnu] ; exact hle.left.ne
  have htc' := fun x y : G'.verts ↦ G'.subgraph_reachable_is_reachable x y (htc x y)
  have hfur := fun x : G'.verts ↦ earliest_edge_reachability hee x (htc' ⟨v, hvin⟩ x)
  have htur := fun x : G'.verts ↦ latest_edge_reachability hle x (htc' x ⟨w, hwin⟩)
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

def EarliestNeigbhor (α u : V) : Prop := ∃ t, G.EarliestEdge α u t

def LatestNeighbor (β u : V) : Prop := ∃ t, G.LatestEdge β u t

def V_minus (G : SimpleTemporalGraph V) : Set V := {u | ∃ α, G.EarliestNeigbhor α u}

def V_plus (G : SimpleTemporalGraph V) : Set V := {u | ∃ β, G.LatestNeighbor β u}

def V_zero (G : SimpleTemporalGraph V) : Set V := {u | u ∉ G.V_minus ∧ u ∉ G.V_plus}

namespace SubTempGraph

section Basics

variable (u : V) (H : SubTempGraph G)

def VMinus : Set V
:= {u | ∃ α, G.EarliestNeigbhor α u ∧ u ∈ H.verts ∧ α ∈ H.verts}

def VPlus : Set V
:= {u | ∃ β, G.LatestNeighbor β u ∧ u ∈ H.verts ∧ β ∈ H.verts}

def VZero : Set V := {u | u ∉ H.VMinus ∧ u ∉ H.VPlus}

def MountableMinusOn := ∃ α, G.EarliestNeigbhor α u ∧ u ∉ H.verts ∧ α ∈ H.verts

lemma vMinus_imp_MountableMinusOn
: u ∈ H.VMinus → MountableMinusOn u (H.deleteVerts {u})
:= by
  intro ⟨α, hen, _, hα⟩
  have hα : α ∈ (H.deleteVerts {u}).verts := by
    simp_rw [EarliestNeigbhor, EarliestEdge] at hen ; have ⟨_, hadj, _⟩ := hen ; simp [hα, hadj.ne]
  have hu_nin : u ∉ (H.deleteVerts {u}).verts := by simp
  exact ⟨α, hen, hu_nin, hα⟩

-- Is it useless?
def MountableMinus := ∃ u, MountableMinusOn u H

def MountablePlusOn := ∃ β, G.LatestNeighbor β u ∧ u ∉ H.verts ∧ β ∈ H.verts

lemma vPlus_imp_MountablePlusOn
: u ∈ H.VPlus → MountablePlusOn u (H.deleteVerts {u})
:= by
  intro ⟨β, hln, _, hβ⟩
  have hβ : β ∈ (H.deleteVerts {u}).verts := by
    simp_rw [LatestNeighbor, LatestEdge] at hln ; have ⟨_, hadj, _⟩ := hln ; simp [hβ, hadj.ne]
  have hu_nin : u ∉ (H.deleteVerts {u}).verts := by simp
  exact ⟨β, hln, hu_nin, hβ⟩

-- useless?
def MountablePlus := ∃ u, MountablePlusOn u H

def MountableOn := MountableMinusOn u H ∧ MountablePlusOn u H

def Mountable := ∃ u, MountableMinusOn u H ∧ MountablePlusOn u H

@[simp]
lemma mountableOn_imp_mountable : MountableOn u H → Mountable H
:= by intro ⟨hₘ, hₚ⟩ ; exact ⟨u, hₘ, hₚ⟩

theorem vMinus_inter_VPlus_imp_mountableOn
: u ∈ (H.VMinus ∩ H.VPlus) → MountableOn u (H.deleteVerts {u})
:= by
  intro ⟨hm, hp⟩
  have hm := vMinus_imp_MountableMinusOn _ _ hm
  have hp := vPlus_imp_MountablePlusOn _ _ hp
  exact ⟨hm, hp⟩

def Mount {α β : V} {t s : ℕ} (H : SubTempGraph G) (u : V)
(hee : G.EarliestEdge α u t ∧ α ∈ H.verts)
(hle : G.LatestEdge β u s ∧ β ∈ H.verts)
: G.SubTempGraph
:=
  have he : G.Adj α u t := hee.left.left
  have he' : G.Adj β u s := hle.left.left
  have hvu : u ∈ (H.addVerts {u}).verts := by simp
  have hv : α ∈ (H.addVerts {u}).verts ∧ u ∈ (H.addVerts {u}).verts := by simp [hee.right]
  have hv' : β ∈ (H.addVerts {u}).verts ∧ u ∈ (H.addVerts {u}).verts := by simp [hle.right]
((H.addVerts {u}).addEdge he hv).addEdge he' hv'

theorem mount_tc {α β : V} {t s : ℕ} (H : SubTempGraph G) (u : V)
(hee : G.EarliestEdge α u t ∧ α ∈ H.verts)
(hle : G.LatestEdge β u s ∧ β ∈ H.verts)
: H.TemporallyConnected → (Mount H u hee hle).TemporallyConnected
:= by sorry


end Basics

section Mountable2

variable (u : V) (H : SubTempGraph G)

def Mountable2MinusOn
:= MountableMinusOn u H
  ∨ ∃ α α' t t', G.EarliestEdge α α' t ∧ G.Adj α u t' ∧ t' ≤ t
    ∧ {α, α'} ⊆ H.verts ∧ u ∉ H.verts

def Mountable2PlusOn
:= MountablePlusOn u H
  ∨ ∃ β β' t t', G.LatestEdge β β' t ∧ G.Adj β' u t' ∧ t ≤ t'
    ∧ {β, β'} ⊆ H.verts ∧ u ∉ H.verts

def Mountable2On := Mountable2MinusOn u H ∨ Mountable2PlusOn u H

def Mountable2 := ∃ u, Mountable2On u H

end Mountable2

end SubTempGraph

end SimpleTemporalGraph
