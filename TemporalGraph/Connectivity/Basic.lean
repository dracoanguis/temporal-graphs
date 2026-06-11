/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.TemporalWalk

universe u
variable {V : Type u}

namespace LooplessTemporalGraph

def Reachable (G : LooplessTemporalGraph V) (x y : V) : Prop :=
  ∃ n m : ℕ, Nonempty (G.TemporalWalk x n y m)

/-- The type of `NonemptyTemporalWalk` is `Nonempty`. -/
theorem reachable_of_nonempty_NonemptyTemporalWalk {G : LooplessTemporalGraph V} {x y : V} :
    (∃ n m : ℕ, Nonempty (G.NonemptyTemporalWalk x n y m)) → G.Reachable x y := by
  intro ⟨n, m, ⟨h⟩⟩
  use n, m, ↑h

theorem reachable_of_self {G : LooplessTemporalGraph V} (x : V) : G.Reachable x x := by
  use 0, 0, TemporalWalk.Empty

abbrev self_reachable {G : LooplessTemporalGraph V} (x : V) := G.reachable_of_self x

theorem reachable_iff_nonempty_univ {G : LooplessTemporalGraph V} {x y : V} :
    G.Reachable x y ↔ ∃ n m : ℕ, (Set.univ : Set (G.TemporalWalk x n y m)).Nonempty := by
  unfold Reachable
  apply Iff.intro
  · intro ⟨n, ⟨m, ⟨p⟩⟩⟩
    exact ⟨n, ⟨m, ⟨p, trivial⟩⟩⟩
  · intro ⟨n, ⟨m, ⟨p, _⟩⟩⟩
    exact ⟨n, ⟨m, ⟨p⟩⟩⟩

theorem reachable_iff_nonempty_temporalWalkSet {G : LooplessTemporalGraph V} {x y : V} :
    G.Reachable x y ↔ (G.TemporalWalkSet x y).Nonempty := by
  apply Iff.intro
  · rintro ⟨n, ⟨m, ⟨p⟩⟩⟩
    exact ⟨⟨n, m, p⟩, ⟨n, m, p, rfl⟩⟩
  · rintro ⟨⟨n, m, p⟩, _⟩
    exact ⟨n, ⟨m, ⟨p⟩⟩⟩

def TemporallyConnected (G : LooplessTemporalGraph V) : Prop := ∀ x y : V, G.Reachable x y

/-- `G'` is a spanner of `G` iff they have the same verticies and everything reachable in `G` is
reachable in `G'`. -/
def IsSpanner {s : Set V} (G : LooplessTemporalGraph V) (G' : LooplessTemporalGraph s) : Prop :=
  (∀ x : V, x ∈ s)
  ∧
  ∀ (x y : V) (hx : x ∈ s) (hy : y ∈ s), G.Reachable x y → G'.Reachable ⟨x, hx⟩ ⟨y, hy⟩

def IsTCSpanner {s : Set V} (G : LooplessTemporalGraph V) (G' : LooplessTemporalGraph s) : Prop :=
  G.IsSpanner G' ∧ G'.TemporallyConnected

theorem temporallyConnected_of_isClique (G : LooplessTemporalGraph V) :
    G.IsClique → G.TemporallyConnected := by
  unfold IsClique TemporallyConnected
  intro h x y
  have h' := h x y
  by_cases hdiff : x ≠ y
  · have ⟨n, h'⟩ := h' hdiff
    exact reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨NonemptyTemporalWalk.Single h'⟩⟩
  · simp_all [reachable_of_self]

lemma reachable_of_earliestEdge {x y : V} {n : ℕ} {G : LooplessTemporalGraph V}
    (h : G.EarliestEdge x y n) :
    ∀ z : V, G.Reachable x z → G.Reachable y z := by
  rw [EarliestEdge] at h
  intro _ ⟨m, _, ⟨p⟩⟩
  cases p with
  | Empty =>
    apply reachable_of_nonempty_NonemptyTemporalWalk ;
    exact ⟨_, _, ⟨NonemptyTemporalWalk.Single h.left.symm⟩⟩
  | Nonempty p =>
    have hst : n ≤ m := NonemptyTemporalWalk.EarliestEdge.time_bound_of_edge p h
    exact reachable_of_nonempty_NonemptyTemporalWalk ⟨_, _, ⟨p.prepend h.left.symm hst⟩⟩

lemma reachable_of_extended_earliestEdge {x y z : V} {n m : ℕ} {G : LooplessTemporalGraph V}
    (h₀ : G.EarliestEdge x y n)
    (h₁ : G.Adj z y m)
    (h₂ : m ≤ n) :
    ∀ a : V, G.Reachable x a → G.Reachable z a := by
  intro _ ⟨k, _, ⟨p⟩⟩
  let p' : NonemptyTemporalWalk z m x n := NonemptyTemporalWalk.Single h₁ |>.Step h₀.left.symm h₂
  cases p with
  | Empty =>
      apply reachable_of_nonempty_NonemptyTemporalWalk ;
      use  m, n, p'
  | Nonempty p =>
    have h : n ≤ k := NonemptyTemporalWalk.EarliestEdge.time_bound_of_edge p h₀
    exact reachable_of_nonempty_NonemptyTemporalWalk ⟨_, _, ⟨p'.append p h⟩⟩

lemma reachable_of_latestEdge {x y : V} {n : ℕ} {G : LooplessTemporalGraph V}
    (h : G.LatestEdge x y n) :
    ∀ z : V, G.Reachable z x → G.Reachable z y := by
  intro _ ⟨_, m, ⟨p⟩⟩
  cases p with
  | Empty =>
    exact reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨NonemptyTemporalWalk.Single h.left⟩⟩
  | Nonempty p =>
    have het : m ≤ n := NonemptyTemporalWalk.LatestEdge.time_bound_of_edge p h
    exact reachable_of_nonempty_NonemptyTemporalWalk ⟨_, _, ⟨p.Step h.left het⟩⟩

lemma reachable_of_extended_latestEdge {x y z : V} {n m : ℕ} {G : LooplessTemporalGraph V}
    (h₀ : G.LatestEdge x y n)
    (h₁ : G.Adj y z m)
    (h₂ : n ≤ m) :
    ∀ a : V, G.Reachable a x → G.Reachable a z := by
  intro _ ⟨_, k, ⟨p⟩⟩
  let p' : NonemptyTemporalWalk x n z m := NonemptyTemporalWalk.Single h₀.left |>.Step h₁ h₂
  cases p with
  | Empty =>
      apply reachable_of_nonempty_NonemptyTemporalWalk ;
      use  n, m, p'
  | Nonempty p =>
    have h : k ≤ n := NonemptyTemporalWalk.LatestEdge.time_bound_of_edge p h₀
    exact reachable_of_nonempty_NonemptyTemporalWalk ⟨_, _, ⟨p.append p' h⟩⟩

end LooplessTemporalGraph
