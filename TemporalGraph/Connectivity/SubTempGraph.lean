import TemporalGraph.Connectivity.Basic
import TemporalGraph.SubTempGraph

universe u
variable {V : Type u} {t : ℕ} {V' : Set V} {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph

namespace SubTempGraph


def IsSpanner (G' : SubTempGraph G) : Prop
:= G'.IsSpanning ∧ ∀ u v : G'.verts, G.Reachable u v → G'.coe.Reachable u v

def TemporallyConnected (G' : SubTempGraph G) : Prop
:= ∀ u v , G'.coe.Reachable u v

def IsTCSpanner (G' : SubTempGraph G) : Prop :=
  (G'.IsSpanning) ∧ (TemporallyConnected G')

protected lemma temporallyConnected_iff {G' : SubTempGraph G}
: G'.TemporallyConnected ↔ G'.coe.TemporallyConnected
:= by
  apply Iff.intro
  · unfold TemporallyConnected
    intro h
    unfold SimpleTemporalGraph.TemporallyConnected
    trivial
  · unfold TemporallyConnected
    intro h
    rw [SimpleTemporalGraph.TemporallyConnected] at h
    trivial

@[simp]
protected lemma subgraph_reachable_is_reachable
{V : Type u} {G : SimpleTemporalGraph V} {G' : SubTempGraph G}
: ∀ u v, G'.coe.Reachable u v → G.Reachable ↑u ↑v
:= by
  intro u v h
  rw [reachable_iff_nonempty_univ] at h
  let ⟨s, ⟨t, ⟨tw, h⟩⟩⟩ := h
  rw [reachable_iff_nonempty_univ]
  exact ⟨s, ⟨t, ⟨tw, h⟩⟩⟩

@[simp]
protected lemma TCspanner_imply_TC (G' : SubTempGraph G)
: G'.IsTCSpanner → G.TemporallyConnected
:= by
  intro ⟨h_span,h_tc⟩
  unfold TemporallyConnected at h_tc
  rw [SubTempGraph.IsSpanning] at h_span
  rw [SimpleTemporalGraph.TemporallyConnected]
  simp [h_span] at h_tc
  intro u v
  let u' : Subtype G'.verts := ⟨u, h_span u⟩
  let v' : Subtype G'.verts := ⟨v, h_span v⟩
  let ⟨s, ⟨t, ⟨tw⟩⟩⟩ :=  h_tc u v
  exact ⟨s, ⟨t, ⟨tw.lift_subtempgraph_walk⟩⟩⟩


-- /-- A temporal graphe admits a spanner if and only if it is Temporally Connected -/
-- @[simp]
-- theorem TCspanner_iff_TC (G : SimpleTemporalGraph V)
-- : (∃ (G' : SubTempGraph G), G'.IsTCSpanner) ↔ G.TemporallyConnected
-- := by
--   unfold SubTempGraph.IsTCSpanner
--   apply Iff.intro
--   · intro ⟨G', ⟨h_span,h_tc⟩⟩
--     unfold TemporallyConnected at h_tc
--     rw [SubTempGraph.IsSpanning] at h_span
--     rw [TemporallyConnected]
--     simp [h_span] at h_tc
--     intro u v
--     let u' : Subtype G'.verts := ⟨u, h_span u⟩
--     let v' : Subtype G'.verts := ⟨v, h_span v⟩
--     let ⟨t, ⟨tw⟩⟩ :=  h_tc u v
--     exact ⟨t, ⟨tw.lift_subtempgraph_walk⟩⟩

--   · intro h_tc
--     let G' : SubTempGraph G := {
--       verts := Set.univ
--       Adj := G.Adj
--       adj_sub := by
--         intro u v t h
--         trivial
--       symm := G.symm
--       edge_vert := by
--         intro v w t h
--         trivial
--     }
--     have h_span : G'.IsSpanning := by
--       rw [SubTempGraph.isSpanning_iff]
--     have h'_tc : G'.coe.TemporallyConnected := by
--       rw [TemporallyConnected]
--       intro u v
--       unfold TemporallyConnected Reachable at h_tc
--       rw [Reachable]

--     exact ⟨G', ⟨h_span, h_tc⟩⟩


lemma tc_construct {u v w : V} {t₁ t₂ : ℕ} (G : SimpleTemporalGraph V) (G' : SubTempGraph G)
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



end SubTempGraph
end SimpleTemporalGraph
