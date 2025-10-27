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
      exact ⟨t, ⟨p, trivial⟩ ⟩
    · intro ⟨t, ⟨p, _⟩⟩
      exact ⟨t, ⟨p⟩⟩


def TemporallyConnected (G : SimpleTemporalGraph V) : Prop := ∀ u v , G.Reachable u v


end SimpleTemporalGraph
