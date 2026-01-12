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
  have huu := earliest_latest_edge_co_reachability hee hle (htc' ⟨v, hvin⟩ ⟨w, hwin⟩)
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

def Mount {α β : V}{t s : ℕ}
(H : SubTempGraph G) (u : V)
(hv₁ : α ∈ H.verts) (hen : G.EarliestNeigbhor α u)
(hv₂ : β ∈ H.verts) (hln : G.LatestNeighbor β u)
: G.SubTempGraph
:=
  have hE₁ := by obtain ⟨_, ⟨he, _⟩⟩ := hen ; exact he
  -- have hV : ∀ x, x ∈ (H.addVerts {u}).verts := by
  --   rw [IsSpannerOf] at hR
  --   let hR := hR.left
  --   rw [deleteVerts_verts] at hR
  --   rw [addVerts_verts, hR, top_verts]
  --   simp
  have hv₁ : α ∈ (H.addVerts {u}).verts ∧ u ∈ (H.addVerts {u}).verts := And.intro (hV α) (hV u)
  have hE₂ : G.Adj β u s := by have ⟨s, ⟨he, _⟩⟩ := hln ; exact he
  have hv₂ : β ∈ (H.addVerts {u}).verts ∧ u ∈ (H.addVerts {u}).verts := And.intro (hV β) (hV u)
((H.addVerts {u}).addEdge hE₁ hv₁).addEdge hE₂ hv₂

def V_minus (G : SimpleTemporalGraph V) : Set V := {u | ∃ α, G.EarliestNeigbhor α u}

def V_plus (G : SimpleTemporalGraph V) : Set V := {u | ∃ β, G.LatestNeighbor β u}

def V_zero (G : SimpleTemporalGraph V) : Set V := {u | u ∉ G.V_minus ∧ u ∉ G.V_plus}

namespace SubTempGraph

def V_minus (H : SubTempGraph G) : Set V
:= {u | ∃ α, G.EarliestNeigbhor α u ∧ u ∈ H.verts ∧ α ∈ H.verts}

def V_plus (H : SubTempGraph G) : Set V
:= {u | ∃ β, G.LatestNeighbor β u ∧ u ∈ H.verts ∧ β ∈ H.verts}

def V_zero (H : SubTempGraph G) : Set V := {u | u ∉ H.V_minus ∧ u ∉ H.V_plus}

def Mountable (H : SubTempGraph G) : Prop
:= ∃ u α β, G.EarliestNeigbhor α u ∧ G.LatestNeighbor β u
  ∧ u ∉ H.verts ∧ {α, β} ⊆ H.verts ∧ H.TemporallyConnected

def MountableOn (u : V) (H : SubTempGraph G) : Prop
:= u ∉ H.verts ∧
  ∃ (α β : H.verts), G.EarliestNeigbhor α u ∧ G.LatestNeighbor β u ∧ H.TemporallyConnected

theorem mountableOn_imp_mountable (u : V) (H : SubTempGraph G)
: MountableOn u H → Mountable H
:= by
  rw [MountableOn, Mountable]
  rintro ⟨hu, ⟨⟨α, hα⟩, ⟨β, hβ⟩, hee, hle, hTC⟩⟩
  have hαβ : {α, β} ⊆ H.verts := by rw [Set.subset_def] ; simpa using And.intro hα hβ
  exact ⟨u, α, β, hee, hle, hu, hαβ, hTC⟩

theorem mountable_construct (H : SubTempGraph G) (hH : Mountable H) : G.TemporallyConnected
:= by
  rw [Mountable] at hH
  have ⟨_, _, _, _, _, h, h', h''⟩ := hH
  exact mountable_construct' G H (And.intro h h') h''

theorem V_minus_inter_V_plus_non_empty_imply_mountableon (u : V) (H : SubTempGraph G)
: u ∈ (H.V_minus ∩ H.V_plus) ∧ (H.deleteVerts {u}).TemporallyConnected
   → MountableOn u (H.deleteVerts {u})
:= by
  rw [MountableOn, V_minus, V_plus]
  intro ⟨hV, hTC⟩
  simp at hV
  have ⟨⟨α, hen, _, hα⟩, ⟨β, hln, _, hβ⟩⟩ := hV
  have hα : α ∈ (H.deleteVerts {u}).verts := by
    simp_rw [EarliestNeigbhor, EarliestEdge] at hen ; have ⟨_, hadj, _⟩ := hen ; simp [hα, hadj.ne]
  have hβ : β ∈ (H.deleteVerts {u}).verts := by
    simp_rw [LatestNeighbor, LatestEdge] at hln ; have ⟨_, hadj, _⟩ := hln ; simp [hβ, hadj.ne]
  have hu_nin : u ∉ (H.deleteVerts {u}).verts := by simp
  exact ⟨hu_nin, ⟨α, hα⟩, ⟨β, hβ⟩, hen, hln, hTC⟩

def Mountable2 (H : SubTempGraph G) : Prop
:= (∃ u α β β' t t', G.EarliestNeigbhor α u ∧ (G.LatestEdge β β' t ∧ G.Adj β' u t' ∧ t ≤ t')
    ∧ u ∉ H.verts ∧ {α, β, β'} ⊆ H.verts)
  ∨ (∃ u α α' β s s', G.LatestNeighbor β u ∧ (G.EarliestEdge α α' s ∧ G.Adj α u s' ∧ s' ≤ s)
    ∧ u ∉ H.verts ∧ {α, α', β} ⊆ H.verts)
  ∨ (∃ u α α' β β' t t' s s', (G.LatestEdge β β' t ∧ G.Adj β' u t' ∧ t ≤ t')
    ∧ (G.EarliestEdge α α' s ∧ G.Adj α u s' ∧ s' ≤ s) ∧ u ∉ H.verts ∧ {α, α', β, β'} ⊆ H.verts)

def Mountable2On (u : V) (H : SubTempGraph G) : Prop
:= u ∉ H.verts ∧ (
  (∃ α β β' t t', G.EarliestNeigbhor α u ∧ (G.LatestEdge β β' t ∧ G.Adj β' u t' ∧ t ≤ t')
    ∧ {α, β, β'} ⊆ H.verts)
  ∨ (∃ u α α' β s s', G.LatestNeighbor β u ∧ (G.EarliestEdge α α' s ∧ G.Adj α u s' ∧ s' ≤ s)
    ∧ {α, α', β} ⊆ H.verts)
  ∨ (∃ u α α' β β' t t' s s', (G.LatestEdge β β' t ∧ G.Adj β' u t' ∧ t ≤ t')
    ∧ (G.EarliestEdge α α' s ∧ G.Adj α u s' ∧ s' ≤ s) ∧ {α, α', β, β'} ⊆ H.verts)
)

end SubTempGraph

end SimpleTemporalGraph
