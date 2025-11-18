import TemporalGraph.TemporalWalk

universe u
variable {V : Type u} {s t : ℕ}

namespace SimpleTemporalGraph

def Reachable (G : SimpleTemporalGraph V) (u v : V) : Prop :=
∃ s t, Nonempty (G.TemporalWalk u s v t)

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

-- theorem spanner_iff_subgraph {V' : Set V} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph V')
-- : G.IsSpanner G' ↔ G.IsSubtempgraph G'
-- := by
--   sorry

def IsTCSpanner {V' : Set V} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph V') : Prop
:= G.IsSpanner G' ∧ G'.TemporallyConnected

theorem complete_is_TC (G : SimpleTemporalGraph V)
: G.IsComplete → G.TemporallyConnected
:= by
  unfold IsComplete TemporallyConnected
  intro h u v
  let ⟨t, h'⟩ := h u v
  rw [reachable_iff_nonempty_univ]
  exact ⟨t, ⟨t, ⟨TemporalWalk.single h', trivial⟩⟩⟩

lemma earliest_edge_reachability {u α : V} {t₁ : ℕ} {G : SimpleTemporalGraph V}
(hee : G.EarliestEdge α u t₁) : ∀ w, G.Reachable α w → G.Reachable u w
:= by
  intro w hTw
  rw [reachable_iff_nonempty_TemporalWalkset] at hTw
  rw [EarliestEdge] at hee
  let ⟨_, s, e, tw, _⟩ := hTw
  have hst : t₁ ≤ s := TemporalWalk.EarliestEdge.edge_time_bound tw hee
  let twu := tw.prepend hee.left.symm hst
  rw [reachable_iff_nonempty_TemporalWalkset]
  exact ⟨⟨t₁, e, twu⟩, ⟨t₁, ⟨e, ⟨twu, rfl⟩⟩⟩⟩

lemma latest_edge_reachability {u α : V} {t₁ : ℕ} {G : SimpleTemporalGraph V}
(hle : G.LatestEdge α u t₁) : ∀ w, G.Reachable w α → G.Reachable w u
:= by
  intro h hTW
  rw [reachable_iff_nonempty_TemporalWalkset] at hTW
  rw [LatestEdge] at hle
  let ⟨_, s, e, tw, _⟩ := hTW
  have het : e ≤ t₁ := TemporalWalk.LatestEdge.edge_time_bound tw hle
  let tuw := tw.step hle.left het
  rw [reachable_iff_nonempty_TemporalWalkset]
  exact ⟨⟨s, t₁, tuw⟩, ⟨s, ⟨t₁, ⟨tuw, rfl⟩⟩⟩⟩


end SimpleTemporalGraph
