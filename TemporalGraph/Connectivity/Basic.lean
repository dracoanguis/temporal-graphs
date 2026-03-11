import TemporalGraph.TemporalWalk

universe u
variable {V : Type u}

namespace SimpleTemporalGraph

def Reachable (G : SimpleTemporalGraph V) (x y : V) : Prop :=
∃ n m : ℕ, Nonempty (G.TemporalWalk x n y m)

theorem reachable_of_nonempty_NonemptyTemporalWalk {G : SimpleTemporalGraph V} {x y : V}
: (∃ n m : ℕ, Nonempty (G.NonemptyTemporalWalk x n y m)) → G.Reachable x y
:= by
  intro ⟨n, m, ⟨h⟩⟩
  use n, m, ↑h

theorem self_reachable {G : SimpleTemporalGraph V} (x : V)
: G.Reachable x x
:= by use 0, 0, TemporalWalk.Empty

theorem reachable_iff_nonempty_univ {G : SimpleTemporalGraph V} {x y : V} :
G.Reachable x y ↔ ∃ n m : ℕ, (Set.univ : Set (G.TemporalWalk x n y m)).Nonempty := by
    unfold Reachable
    apply Iff.intro
    · intro ⟨n, ⟨m, ⟨p⟩⟩⟩
      exact ⟨n, ⟨m, ⟨p, trivial⟩⟩⟩
    · intro ⟨n, ⟨m, ⟨p, _⟩⟩⟩
      exact ⟨n, ⟨m, ⟨p⟩⟩⟩

theorem reachable_iff_nonempty_temporalWalkSet {G : SimpleTemporalGraph V} {x y : V} :
G.Reachable x y ↔ (G.TemporalWalkSet x y).Nonempty := by
  apply Iff.intro
  · rintro ⟨n, ⟨m, ⟨p⟩⟩⟩
    exact ⟨⟨n, m, p⟩, ⟨n, m, p, rfl⟩⟩
  · rintro ⟨⟨n, m, p⟩, _⟩
    exact ⟨n, ⟨m, ⟨p⟩⟩⟩

def TemporallyConnected (G : SimpleTemporalGraph V) : Prop := ∀ x y : V, G.Reachable x y

def IsSpanner {s : Set V} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph s) : Prop
:=  (∀ x : V, x ∈ s)
  ∧ ∀ (x y : V) (hx : x ∈ s) (hy : y ∈ s), G.Reachable x y → G'.Reachable ⟨x, hx⟩ ⟨y, hy⟩

def IsTCSpanner {s : Set V} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph s) : Prop
:= G.IsSpanner G' ∧ G'.TemporallyConnected

theorem temporallyConnected_of_complete (G : SimpleTemporalGraph V)
: G.IsComplete → G.TemporallyConnected
:= by
  unfold IsComplete TemporallyConnected
  intro h x y
  have h' := h x y
  by_cases hdiff : x ≠ y
  · have ⟨n, h'⟩ := h' hdiff
    exact reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨NonemptyTemporalWalk.Single h'⟩⟩
  · simp_all [self_reachable]

lemma reachable_of_earliestEdge {x y : V} {n : ℕ} {G : SimpleTemporalGraph V}
(h : G.EarliestEdge x y n) : ∀ z : V, G.Reachable x z → G.Reachable y z
:= by
  rw [EarliestEdge] at h
  intro _ ⟨m, _, ⟨p⟩⟩
  cases p with
  | Empty =>
    apply reachable_of_nonempty_NonemptyTemporalWalk ;
    exact ⟨_, _, ⟨NonemptyTemporalWalk.Single h.left.symm⟩⟩
  | Nonempty p =>
    have hst : n ≤ m := NonemptyTemporalWalk.EarliestEdge.time_bound_of_edge p h
    exact reachable_of_nonempty_NonemptyTemporalWalk ⟨_, _, ⟨p.prepend h.left.symm hst⟩⟩


lemma reachable_of_latestEdge {x y : V} {n : ℕ} {G : SimpleTemporalGraph V}
(h : G.LatestEdge x y n) : ∀ z : V, G.Reachable z x → G.Reachable z y
:= by
  intro _ ⟨_, m, ⟨p⟩⟩
  cases p with
  | Empty =>
    exact reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨NonemptyTemporalWalk.Single h.left⟩⟩
  | Nonempty p =>
    have het : m ≤ n := NonemptyTemporalWalk.LatestEdge.time_bound_of_edge p h
    exact reachable_of_nonempty_NonemptyTemporalWalk ⟨_, _, ⟨p.Step h.left het⟩⟩

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
