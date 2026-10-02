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
* `mapLe` : Transport a walk along a spanning-subgraph inclusion `G ≤ G'`

## Main results
* `nondecreasing_time` : Times are non-decreasing along a walk
* `length_mapLe`, `support_mapLe`, `arcs_mapLe` : Mapping preserves length, support and arcs
* `start_mem_support`, `end_mem_support` : Walk endpoints belong to the support
* `adj_of_mem_arcs` : Every arc in a walk is an edge within the time bounds
-/

universe u

variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

/-- We define a Non-strict TemporalWalk, meaning multiple edges can be crossed at a given time. -/
inductive TemporalWalk : V → ℕ → V → ℕ → Type u
  | Empty {x : V} {n : ℕ} : TemporalWalk x n x n
  | Nonempty {x y : V} {n m : ℕ} (p : G.NonemptyTemporalWalk x n y m) : TemporalWalk x n y m
  deriving DecidableEq

/-- The set of all `(n, m, walk)` triples witnessing a temporal walk from `x` to `y`, over every
pair of start/end times. -/
def temporalWalkSet (x y : V) :
    Set (Σ n m : ℕ, G.TemporalWalk x n y m) :=
  { p | ∃ (n m : ℕ), ∃ (tw : TemporalWalk x n y m), p = ⟨n, m, tw⟩ }

namespace TemporalWalk

/-- The length of a TemporalWalk is the number of edges along it. -/
@[grind =]
def length {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → ℕ
  | Empty => 0
  | Nonempty p => p.length

/-- The `support` of a TemporalWalk is the list of vertices it visits in order. -/
@[grind =]
def support {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → List V
  | Empty => [x]
  | Nonempty p => p.support


/-- The `arcs` of a TemporalWalk is the list of arcs (edge with a direction) it visits in
order. -/
@[grind =]
def arcs {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → List (V × V × ℕ)
  | Empty => []
  | Nonempty p => p.arcs

/-- Times are non-decreasing along a (possibly empty) walk: `n ≤ m`. -/
@[simp]
lemma nondecreasing_time {x y : V} {n m : ℕ} (tw : G.TemporalWalk x n y m) : n ≤ m := by
  cases tw with
  | Empty => trivial
  | Nonempty p => exact p.nondecreasing_time

/-- Map a walk along `G ≤ G'`, following `NonemptyTemporalWalk.mapLe`. -/
@[grind =]
protected def mapLe {G' : TemporalGraph V} (h : G ≤ G') {x y : V} {n m : ℕ} :
    G.TemporalWalk x n y m → G'.TemporalWalk x n y m
  | Empty => Empty
  | Nonempty p => Nonempty (p.mapLe h)

section API

variable {x y : V} {n m : ℕ}

/-- Mapping a walk along `G ≤ G'` preserves its length. -/
@[simp, grind =]
theorem length_mapLe {G' : TemporalGraph V} (h₀ : G ≤ G') (p : G.TemporalWalk x n y m) :
    (p.mapLe h₀).length = p.length := by
  cases p <;> grind

/-- Mapping a walk along `G ≤ G'` preserves its support. -/
@[simp, grind =]
theorem support_mapLe {G' : TemporalGraph V} (h₀ : G ≤ G') (p : G.TemporalWalk x n y m) :
    (p.mapLe h₀).support = p.support := by
  cases p <;> grind

/-- Mapping a walk along `G ≤ G'` preserves its arcs. -/
@[simp, grind =]
theorem arcs_mapLe {G' : TemporalGraph V} (h₀ : G ≤ G') (p : G.TemporalWalk x n y m) :
    (p.mapLe h₀).arcs = p.arcs := by
  cases p <;> grind

/-- The start vertex of a walk belongs to its support. -/
@[grind .]
theorem start_mem_support (p : G.TemporalWalk x n y m) : x ∈ p.support := by
  cases p <;> grind

/-- The end vertex of a walk belongs to its support. -/
@[grind .]
theorem end_mem_support (p : G.TemporalWalk x n y m) : y ∈ p.support := by
  cases p <;> grind

/-- Every arc of a walk is an edge of the graph, at a time between the start and end times. -/
theorem adj_of_mem_arcs (p : G.TemporalWalk x n y m) :
    ∀ a ∈ p.arcs, G.Adj a.1 a.2.1 a.2.2 ∧ n ≤ a.2.2 ∧ a.2.2 ≤ m := by
  cases p with
  | Empty => grind only [arcs, ← List.not_mem_nil]
  | Nonempty p => exact p.adj_of_mem_arcs

end API

end TemporalWalk

namespace NonemptyTemporalWalk

-- Auto coercion to a TemporalWalk since they are never empty
instance {x y : V} {n m : ℕ} : Coe (G.NonemptyTemporalWalk x n y m) (G.TemporalWalk x n y m) where
  coe  p := TemporalWalk.Nonempty p

end NonemptyTemporalWalk

end TemporalGraph
