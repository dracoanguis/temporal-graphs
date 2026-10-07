/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.NonemptyTemporalWalk

/-!
# Temporal Walks

Defines `TemporalWalk`, an inductive type for temporal walks that may be empty. It wraps
`NonemptyTemporalWalk` or represents an empty walk at a single vertex and time.

## Main definitions
* `TemporalWalk` : A (possibly empty) walk with non-decreasing times
* `length` : The number of edges
* `support` : The list of vertices visited, stored from the end vertex back to the start
* `arcs` : The list of directed edges, stored last arc first
* `IsStrict` : The walk's times increase strictly from each arc to the next
* `mapLe` : Transport a walk along a spanning-subgraph inclusion `G ≤ G'`

## Main results
* `nondecreasing_time` : Times are non-decreasing along a walk
* `length_mapLe`, `support_mapLe`, `arcs_mapLe` : Mapping preserves length, support and arcs
* `isStrict_mapLe`, `isStrict_nonempty` : Strictness is preserved by `mapLe` and by the coercion
  from `NonemptyTemporalWalk`
* `NonemptyTemporalWalk.exists_isStrict` : In a proper symmetric graph, every walk can be shortened
  into a strict one
* `start_mem_support`, `end_mem_support` : Walk endpoints belong to the support
* `adj_of_mem_arcs` : Every arc in a walk is an edge within the time bounds
-/

@[expose] public section

universe u

variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

/-- We define a Non-strict TemporalWalk, meaning multiple edges can be crossed at a given time. -/
inductive TemporalWalk : V → ℕ → V → ℕ → Type u
  | Empty {x : V} {n : ℕ} : TemporalWalk x n x n
  | Nonempty {x y : V} {n m : ℕ} (p : G.NonemptyTemporalWalk x n y m) : TemporalWalk x n y m
  deriving DecidableEq

namespace TemporalWalk

/-- The length of a TemporalWalk is the number of edges along it. -/
@[grind =]
def length {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → ℕ
  | Empty => 0
  | Nonempty p => p.length

/-- The `support` of a TemporalWalk is the list of vertices it visits, stored from the end vertex
back to the start vertex. -/
@[grind =]
def support {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → List V
  | Empty => [x]
  | Nonempty p => p.support


/-- The `arcs` of a TemporalWalk is the list of arcs (edge with a direction) it traverses, stored
last arc first. -/
@[grind =]
def arcs {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → List (V × V × ℕ)
  | Empty => []
  | Nonempty p => p.arcs

/-- Times are non-decreasing along a (possibly empty) walk: `n ≤ m`. -/
lemma nondecreasing_time {x y : V} {n m : ℕ} (tw : G.TemporalWalk x n y m) : n ≤ m := by
  cases tw with
  | Empty => trivial
  | Nonempty p => exact p.nondecreasing_time

/-- A (possibly empty) walk is *strict* when its times increase strictly from each arc to the
next, following `NonemptyTemporalWalk.IsStrict`. The empty walk is strict. -/
@[grind =]
def IsStrict {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → Prop
  | Empty => True
  | Nonempty p => p.IsStrict

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

/-- Mapping a walk along `G ≤ G'` preserves strictness. -/
@[simp, grind =]
theorem isStrict_mapLe {G' : TemporalGraph V} (h₀ : G ≤ G') (p : G.TemporalWalk x n y m) :
    (p.mapLe h₀).IsStrict ↔ p.IsStrict := by
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

/-- Automatic coercion of a `NonemptyTemporalWalk` to a `TemporalWalk`, since it is never empty. -/
instance {x y : V} {n m : ℕ} : Coe (G.NonemptyTemporalWalk x n y m) (G.TemporalWalk x n y m) where
  coe  p := TemporalWalk.Nonempty p

/-- Seen as a `TemporalWalk`, a nonempty walk keeps its strictness. -/
@[simp, grind =]
theorem isStrict_nonempty {x y : V} {n m : ℕ} (p : G.NonemptyTemporalWalk x n y m) :
    (TemporalWalk.Nonempty p).IsStrict ↔ p.IsStrict :=
  Iff.rfl

/-- In a proper symmetric graph, every non-strict walk can be shortened into a strict one with the
same endpoints, starting no earlier and ending no later. Two consecutive arcs `w → y → z` at the
same time are, by properness of the symmetric graph, the same edge crossed back and forth
(`w = z`): the shortening deletes such round trips, and may leave the empty walk. -/
theorem exists_isStrict [G.IsSymm] {x y : V} {n m : ℕ} (h₀ : G.IsProper)
    (p : G.NonemptyTemporalWalk x n y m) :
    ∃ n' m', ∃ q : G.TemporalWalk x n' y m', q.IsStrict ∧ n ≤ n' ∧ m' ≤ m := by
  induction p with
  | Single h => exact ⟨_, _, .Nonempty (.Single h), trivial, le_rfl, le_rfl⟩
  | @Step y z n m k p h h₁ ih =>
    obtain ⟨n', m', q, hq, hn, hm⟩ := ih
    cases q with
    | Empty => exact ⟨k, k, .Nonempty (.Single h), trivial, p.nondecreasing_time.trans h₁, le_rfl⟩
    | Nonempty q =>
      by_cases hlt : m' < k
      · exact ⟨n', k, .Nonempty (q.Step h hlt.le), ⟨hlt, hq⟩, hn, le_rfl⟩
      obtain rfl : m' = k := by omega
      cases q with
      | Single h₂ =>
        -- the walk is `x → y → z` at a single time: a round trip, so `z = x`
        obtain rfl := h₀ y x z n' ⟨h₂.symm, h⟩
        exact ⟨n', n', .Empty, trivial, hn, le_rfl⟩
      | Step q h₂ h₃ =>
        -- the last two arcs `w → y → z` share their time: a round trip, so `z = w`
        obtain rfl := h₀ _ _ z m' ⟨h₂.symm, h⟩
        exact ⟨n', _, .Nonempty q, hq.2, hn, h₃⟩

end NonemptyTemporalWalk

end TemporalGraph
