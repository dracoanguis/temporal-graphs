/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic

/-!
# Nonempty Temporal Walks

Defines `NonemptyTemporalWalk`, an inductive type for temporal walks that are guaranteed
to contain at least one edge. Times must be non-decreasing along the walk.

## Main definitions
* `NonemptyTemporalWalk` : A walk with at least one edge and non-decreasing times
* `length` : The number of edges in a walk
* `support` : The list of vertices visited
* `arcs` : The list of directed edges (as triples `V × V × ℕ`)
* `append` : Concatenate two compatible walks
* `prepend` : Add an edge at the start of a walk
-/

universe u

namespace TemporalGraph

variable {V : Type u} {G : TemporalGraph V}

/-- This is a Nonempty Non-strict TemporalWalk. -/
inductive NonemptyTemporalWalk : V → ℕ → V → ℕ → Type u
  | Single {x y : V} {n : ℕ} (h: G.Adj x y n) : NonemptyTemporalWalk x n y n
  | Step {x y z : V} {n m k : ℕ}
    (p : NonemptyTemporalWalk x n y m) (h : G.Adj y z k) (h' : m ≤ k := by decide) :
    NonemptyTemporalWalk x n z k
  deriving DecidableEq

namespace NonemptyTemporalWalk

/-- The length of a NonemptyTemporalWalk is the number of edges along it. -/
def length {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → ℕ
  | Single _ => 1
  | Step p _ _ => 1 + p.length

/-- The `support` of a NonemptyTemporalWalk is the list of vertices it visits in order. -/
def support {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → List V
  | Single _ => y :: [x]
  | Step p _ _ => y :: p.support

-- Arcs
/-- The `arcs` of a NonemptyTemporalWalk is the list of arcs (edge with a direction) it visits in
order. -/
def arcs {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → List (V × V × ℕ)
  | @Single _ _ x y n _ => [⟨x ,⟨y, n⟩⟩]
  | @Step _ _ _ y z _ _ k p _ _ => ⟨y ,⟨ z, k⟩⟩ :: p.arcs

/-- Concatenate two compatible NonemptyTemporalWalks. -/
def append {x y z : V} {n m k l}
    (p : G.NonemptyTemporalWalk x n y m) (ext : G.NonemptyTemporalWalk y k z l)
    (h : m ≤ k := by decide) :
    G.NonemptyTemporalWalk x n z l :=
  match ext with
  | Single h_edge => p.Step h_edge h
  | Step p' h_edge h_ord' => Step (append p p' h) h_edge h_ord'

/-- The reversed version of `NonemptyTemporalWalk.Step`, concatening an edge at the start of a
walk. -/
def prepend {x y z : V} {n m k : ℕ}
    (p : G.NonemptyTemporalWalk x n y m) (h : G.Adj z x k) (h' : k ≤ n := by decide) :
    G.NonemptyTemporalWalk z k y m :=
  append (Single h) p h'

@[simp]
lemma nondecreasing_time {x y : V} {n m : ℕ} (tw : G.NonemptyTemporalWalk x n y m) : n ≤ m := by
  induction tw with
  | Single h => rfl
  | Step h p h' ih => exact le_trans ih h'

lemma EarliestEdge.time_bound_of_edge {x y z : V} {n m k : ℕ}
    (tw : G.NonemptyTemporalWalk x n y m) (h : G.EarliestEdge x z k) :
    k ≤ n := by
  rw [EarliestEdge] at h
  induction tw with
  |Single h' => exact h.right _ _ h'
  |Step _ _ _ hi => exact hi

lemma LatestEdge.time_bound_of_edge {x y z : V} {n m k : ℕ} [G.IsSymm]
    (tw : G.NonemptyTemporalWalk x n y m) (h : G.LatestEdge y z k) :
    m ≤ k := by
  rw [LatestEdge] at h
  cases tw with
  | Single h' => exact h.right _ _ h'.symm
  | Step _ h' _ => exact h.right _ _ h'.symm


end NonemptyTemporalWalk

end TemporalGraph
