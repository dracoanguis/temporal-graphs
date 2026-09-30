/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.NonemptyTemporalWalk

/-!
# Temporal Walks

Defines `TemporalWalk`, an inductive type for temporal walks that may be empty. It wraps
`NonemptyTemporalWalk` or represents an empty walk at a single vertex and time.

## Main definitions
* `TemporalWalk` : A (possibly empty) walk with non-decreasing times
* `length` : The number of edges
* `support` : The list of vertices visited
* `arcs` : The list of directed edges
* `temporalWalkSet` : The set of all walks between two vertices
-/

universe u

variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

/-- We define a Non-strict TemporalWalk, meaning multiple edges can be crossed at a given time. -/
inductive TemporalWalk : V → ℕ → V → ℕ → Type u
  | Empty {x : V} {n : ℕ} : TemporalWalk x n x n
  | Nonempty {x y : V} {n m : ℕ} (p : G.NonemptyTemporalWalk x n y m) : TemporalWalk x n y m
  deriving DecidableEq

-- Juste pluriels
def temporalWalkSet (x y : V) :
    Set (Σ n m : ℕ, G.TemporalWalk x n y m) :=
  { p | ∃ (n m : ℕ), ∃ (tw : TemporalWalk x n y m), p = ⟨n, m, tw⟩ }

namespace TemporalWalk

/-- The length of a TemporalWalk is the number of edges along it. -/
def length {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → ℕ
  | Empty => 0
  | Nonempty p => p.length

/-- The `support` of a TemporalWalk is the list of vertices it visits in order. -/
def support {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → List V
  | Empty => [x]
  | Nonempty p => p.support


/-- The `arcs` of a TemporalWalk is the list of arcs (edge with a direction) it visits in
order. -/
def arcs {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → List (V × V × ℕ)
  | Empty => []
  | Nonempty p => p.arcs

@[simp]
lemma nondecreasing_time {x y : V} {n m : ℕ} (tw : G.TemporalWalk x n y m) : n ≤ m := by
  cases tw with
  | Empty => trivial
  | Nonempty p => exact p.nondecreasing_time

/-- Map a walk along `G ≤ G'`, following `NonemptyTemporalWalk.mapLe`. -/
protected def mapLe {G' : TemporalGraph V} (h : G ≤ G') {x y : V} {n m : ℕ} :
    G.TemporalWalk x n y m → G'.TemporalWalk x n y m
  | Empty => Empty
  | Nonempty p => Nonempty (p.mapLe h)

end TemporalWalk

namespace NonemptyTemporalWalk

-- Auto coercion to a TemporalWalk since they are never empty
instance {x y : V} {n m : ℕ} : Coe (G.NonemptyTemporalWalk x n y m) (G.TemporalWalk x n y m) where
  coe  p := TemporalWalk.Nonempty p

end NonemptyTemporalWalk

end TemporalGraph
