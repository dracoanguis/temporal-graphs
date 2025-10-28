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

def IsTemporalSpanner (G G' : SimpleTemporalGraph V) : Prop := (G' ≤ G) ∧ (G'.TemporallyConnected)

/-- A temporal graphe admits a spanner if and only if it is Temporally Connected -/
theorem spanner_iff_TC (G : SimpleTemporalGraph V) : (∃ G', G.IsTemporalSpanner G') ↔ G.TemporallyConnected := by
  unfold IsTemporalSpanner
  apply Iff.intro
  · intro ⟨G', ⟨h_sub, h_tc⟩⟩
    unfold TemporallyConnected


  · intro h_tc
    exact ⟨G, ⟨G.isSubtempgraph_self, h_tc⟩ ⟩


end SimpleTemporalGraph
