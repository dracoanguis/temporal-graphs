import TemporalGraph.TimeWalk

universe u
variable {V : Type u} {t : ℕ}

namespace SimpleTemporalGraph

def Reachable (G : SimpleTemporalGraph V) (u v : V) : Prop :=
∃ t, Nonempty (G.TimeWalk u v t)

theorem reachable_iff_nonempty_univ {G : SimpleTemporalGraph V} {u v : V} :
G.Reachable u v ↔ ∃ t, (Set.univ : Set (G.TimeWalk u v t)).Nonempty := by
    unfold Reachable
    apply Iff.intro
    · intro ⟨t, ⟨p⟩⟩
      exact ⟨t, ⟨p, trivial⟩⟩
    · intro ⟨t, ⟨p, _⟩⟩
      exact ⟨t, ⟨p⟩⟩

def TemporallyConnected (G : SimpleTemporalGraph V) : Prop := ∀ u v , G.Reachable u v

def IsSpanner {V' : Set V} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph V') : Prop
:= (∀ v : V, v ∈ V') ∧
  ∀ (u v : V) (hu : u ∈ V') (hv : v ∈ V'), G.Reachable u v → G'.Reachable ⟨u, hu⟩ ⟨v, hv⟩

theorem spanner_iff_subgraph {V' : Set V} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph V')
: G.IsSpanner G' ↔ G.IsSubtempgraph G'
:= by
  sorry

def IsTCSpanner {V' : Set V} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph V') : Prop
:= G.IsSpanner G' ∧ G'.TemporallyConnected

theorem complete_is_TC (G : SimpleTemporalGraph V)
: G.IsComplete → G.TemporallyConnected
:= by
  unfold IsComplete TemporallyConnected
  intro h u v
  let ⟨t, h'⟩ := h u v
  rw [reachable_iff_nonempty_univ]
  exact ⟨t, ⟨TimeWalk.single h', trivial⟩⟩

end SimpleTemporalGraph
