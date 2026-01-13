import TemporalGraph.TemporalWalk

universe u
variable {V : Type u} {s t : ℕ}

namespace SimpleTemporalGraph

def Reachable (G : SimpleTemporalGraph V) (u v : V) : Prop :=
∃ s t, Nonempty (G.TemporalWalk u s v t)

theorem nonempty_NETemporalWalk_imp {G : SimpleTemporalGraph V} {u v : V}
: (∃ s e, Nonempty (G.NETemporalWalk u s v e)) → G.Reachable u v
:= by
  intro ⟨s, t, ⟨h⟩⟩
  use s, t, TemporalWalk.nonempty h

theorem self_reachable {G : SimpleTemporalGraph V} (u : V)
: G.Reachable u u
:= by use 0, 0, TemporalWalk.empty

theorem reachable_iff_nonempty_univ {G : SimpleTemporalGraph V} {u v : V} :
G.Reachable u v ↔ ∃ s t, (Set.univ : Set (G.TemporalWalk u s v t)).Nonempty := by
    unfold Reachable
    apply Iff.intro
    · intro ⟨s, ⟨t,⟨ p⟩⟩⟩
      exact ⟨s, ⟨t, ⟨p, trivial⟩⟩⟩
    · intro ⟨s, ⟨t,⟨p, _⟩⟩⟩
      exact ⟨s, ⟨t, ⟨p⟩⟩⟩

theorem reachable_iff_nonempty_TemporalWalkset {G : SimpleTemporalGraph V} {u v : V} :
G.Reachable u v ↔ (G.TemporalWalkSet u v).Nonempty := by
  apply Iff.intro
  · rintro ⟨s, ⟨t, ⟨tw⟩⟩⟩
    exact ⟨⟨s, t, tw⟩, ⟨s, t, tw, rfl⟩⟩
  · rintro ⟨⟨s, t, tw⟩, _⟩
    exact ⟨s, ⟨t, ⟨tw⟩⟩⟩

def TemporallyConnected (G : SimpleTemporalGraph V) : Prop := ∀ u v , G.Reachable u v

def IsSpanner {V' : Set V} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph V') : Prop
:= (∀ v : V, v ∈ V') ∧
  ∀ (u v : V) (hu : u ∈ V') (hv : v ∈ V'), G.Reachable u v → G'.Reachable ⟨u, hu⟩ ⟨v, hv⟩

def IsTCSpanner {V' : Set V} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph V') : Prop
:= G.IsSpanner G' ∧ G'.TemporallyConnected

theorem complete_is_TC (G : SimpleTemporalGraph V)
: G.IsComplete → G.TemporallyConnected
:= by
  unfold IsComplete TemporallyConnected
  intro h u v
  let ⟨t, h'⟩ := h u v
  exact nonempty_NETemporalWalk_imp ⟨t, t, ⟨NETemporalWalk.single h'⟩⟩

lemma earliest_edge_reachability {u α : V} {t : ℕ} {G : SimpleTemporalGraph V}
(hee : G.EarliestEdge α u t) : ∀ w, G.Reachable α w → G.Reachable u w
:= by
  rw [EarliestEdge] at hee
  intro w ⟨s, e, ⟨tw⟩⟩
  cases tw with
  | empty => exact nonempty_NETemporalWalk_imp ⟨t, t, ⟨NETemporalWalk.single hee.left.symm⟩⟩
  | nonempty p =>
    have hst : t ≤ s := NETemporalWalk.EarliestEdge.edge_time_bound p hee
    exact nonempty_NETemporalWalk_imp ⟨_, _, ⟨p.prepend hee.left.symm hst⟩⟩


lemma latest_edge_reachability {u α : V} {t : ℕ} {G : SimpleTemporalGraph V}
(hle : G.LatestEdge α u t) : ∀ w, G.Reachable w α → G.Reachable w u
:= by
  intro w ⟨s, e, ⟨tw⟩⟩
  cases tw with
  | empty => exact nonempty_NETemporalWalk_imp ⟨t, t, ⟨NETemporalWalk.single hle.left⟩⟩
  | nonempty p =>
    have het : e ≤ t := NETemporalWalk.LatestEdge.edge_time_bound p hle
    exact nonempty_NETemporalWalk_imp ⟨_, _, ⟨p.step hle.left het⟩⟩

-- lemma earliest_latest_edge_co_reachability {u αₑ αₗ : V} {tₑ tₗ : ℕ} {G : SimpleTemporalGraph V}
-- (hee : G.EarliestEdge αₑ u tₑ) (hle : G.LatestEdge αₗ u tₗ) (hr : G.Reachable αₑ αₗ)
-- : G.Reachable u u
-- := by
--   rw [EarliestEdge] at hee
--   rw [LatestEdge] at hle
--   rw [reachable_iff_nonempty_TemporalWalkset] at hr
--   rcases hr with ⟨_, s, e, tw, _⟩
--   let tw' := tw.prepend hee.left.symm (TemporalWalk.EarliestEdge.edge_time_bound tw hee)
--   let tw'' := tw'.step hle.left (TemporalWalk.LatestEdge.edge_time_bound tw' hle)
--   rw [reachable_iff_nonempty_TemporalWalkset]
--   exact ⟨⟨tₑ, tₗ, tw''⟩, ⟨tₑ, ⟨tₗ, ⟨tw'', rfl⟩⟩⟩⟩

end SimpleTemporalGraph
