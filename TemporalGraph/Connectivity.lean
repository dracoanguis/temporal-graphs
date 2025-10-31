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

lemma lift_subtempgraph_reachable (G G' : SimpleTemporalGraph V)
: G' ≤ G → ∀ u v : V, G'.Reachable u v → G.Reachable u v
:= by
  intro h_sub u v
  rw [reachable_iff_nonempty_univ]
  intro ⟨t', ⟨tw', h'⟩⟩
  rw [reachable_iff_nonempty_univ]
  exact ⟨t',⟨TimeWalk.lift_subtempgraph_walk G G' h_sub tw', h'⟩⟩


def TemporallyConnected (G : SimpleTemporalGraph V) : Prop := ∀ u v , G.Reachable u v

def IsTemporalSpanner (G G' : SimpleTemporalGraph V) : Prop := (G' ≤ G) ∧ (G'.TemporallyConnected)

/-- A temporal graphe admits a spanner if and only if it is Temporally Connected -/
@[simp]
theorem spanner_iff_TC (G : SimpleTemporalGraph V)
: (∃ G', IsTemporalSpanner G G') ↔ G.TemporallyConnected
:= by
  unfold IsTemporalSpanner
  apply Iff.intro
  · intro ⟨G', ⟨h_sub,h_tc⟩⟩
    unfold TemporallyConnected at h_tc
    intro u v
    exact lift_subtempgraph_reachable G G' h_sub u v (h_tc u v)
  · intro h_tc
    exact ⟨G, ⟨G.isSubtempgraph_self, h_tc⟩ ⟩


theorem complete_is_TC (G : SimpleTemporalGraph V)
: G.IsComplete → G.TemporallyConnected
:= by
  unfold IsComplete TemporallyConnected
  intro h u v
  let ⟨t, h'⟩ := h u v
  rw [reachable_iff_nonempty_univ]
  exact ⟨t, ⟨TimeWalk.single h', trivial⟩⟩

end SimpleTemporalGraph
