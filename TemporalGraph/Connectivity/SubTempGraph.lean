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
  let ⟨t, ⟨tw, h⟩⟩ := h
  rw [reachable_iff_nonempty_univ]
  exact ⟨t, ⟨tw, h⟩⟩

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
  let ⟨t, ⟨tw⟩⟩ :=  h_tc u v
  exact ⟨t, ⟨tw.lift_subtempgraph_walk⟩⟩


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

end SubTempGraph
end SimpleTemporalGraph
