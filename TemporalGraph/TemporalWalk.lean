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
* `edges` : The list of edges (unordered pairs with their times), stored last edge first
* `IsStrict` : The walk's times increase strictly from each arc to the next
* `transfer` : The same walk, seen in another graph containing all of its arcs
* `mapLe` : Transport a walk along a spanning-subgraph inclusion `G ≤ G'`

## Main results
* `nondecreasing_time` : Times are non-decreasing along a walk
* `length_mapLe`, `support_mapLe`, `arcs_mapLe` : Mapping preserves length, support and arcs
* `isStrict_mapLe`, `isStrict_ofNonempty` : Strictness is preserved by `mapLe` and by the coercion
  from `NonemptyTemporalWalk`
* `NonemptyTemporalWalk.exists_isStrict` : In a proper symmetric graph, every walk can be shortened
  into a strict one
* `start_mem_support`, `end_mem_support` : Walk endpoints belong to the support
* `adj_of_mem_arcs` : Every arc in a walk is an edge within the time bounds
* `length_arcs`, `length_edges` : The lists of arcs and edges have the walk's length
* `ncard_setOf_mem_edges_le` : A walk traverses at most `p.length` distinct edges
* `edges_subset_edgeSet` : The edges of a walk are edges of the graph
* `adj_of_edges_subset` : A walk whose edges lie in a symmetric graph `G'` has its arcs in `G'`
-/

@[expose] public section

universe u

variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

/-- We define a Non-strict TemporalWalk, meaning multiple edges can be crossed at a given time. -/
inductive TemporalWalk : V → ℕ → V → ℕ → Type u
  | nil {x : V} {n : ℕ} : TemporalWalk x n x n
  | ofNonempty {x y : V} {n m : ℕ} (p : G.NonemptyTemporalWalk x n y m) : TemporalWalk x n y m
  deriving DecidableEq

namespace TemporalWalk

/-- The length of a TemporalWalk is the number of edges along it. -/
@[grind =]
def length {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → ℕ
  | nil => 0
  | ofNonempty p => p.length

/-- The `support` of a TemporalWalk is the list of vertices it visits, stored from the end vertex
back to the start vertex. -/
@[grind =]
def support {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → List V
  | nil => [x]
  | ofNonempty p => p.support


/-- The `arcs` of a TemporalWalk is the list of arcs (edge with a direction) it traverses, stored
last arc first. -/
@[grind =]
def arcs {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → List (V × V × ℕ)
  | nil => []
  | ofNonempty p => p.arcs

/-- The `edges` of a TemporalWalk are the edges (unordered pairs, with their times) it traverses,
stored last edge first. -/
@[grind =]
def edges {x y : V} {n m : ℕ} (p : G.TemporalWalk x n y m) : List (Sym2 V × ℕ) :=
  p.arcs.map fun a ↦ (s(a.1, a.2.1), a.2.2)

/-- Times are non-decreasing along a (possibly empty) walk: `n ≤ m`. -/
lemma nondecreasing_time {x y : V} {n m : ℕ} (tw : G.TemporalWalk x n y m) : n ≤ m := by
  cases tw with
  | nil => trivial
  | ofNonempty p => exact p.nondecreasing_time

/-- A (possibly empty) walk is *strict* when its times increase strictly from each arc to the
next, following `NonemptyTemporalWalk.IsStrict`. The empty walk is strict. -/
@[grind =]
def IsStrict {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → Prop
  | nil => True
  | ofNonempty p => p.IsStrict

/-- Map a walk along `G ≤ G'`, following `NonemptyTemporalWalk.mapLe`. -/
@[grind =]
protected def mapLe {G' : TemporalGraph V} (h : G ≤ G') {x y : V} {n m : ℕ} :
    G.TemporalWalk x n y m → G'.TemporalWalk x n y m
  | nil => nil
  | ofNonempty p => ofNonempty (p.mapLe h)

/-- The same walk, seen in another graph `G'` that contains all of its arcs. -/
protected def transfer {x y : V} {n m : ℕ} (p : G.TemporalWalk x n y m)
    (G' : TemporalGraph V) (h₀ : ∀ a ∈ p.arcs, G'.Adj a.1 a.2.1 a.2.2) :
    G'.TemporalWalk x n y m :=
  match p with
  | nil => nil
  | ofNonempty p => ofNonempty (p.transfer G' h₀)

section API

variable {x y : V} {n m : ℕ}

/-- The list of arcs of a walk has as many entries as the walk's length. -/
@[simp, grind =]
theorem length_arcs (p : G.TemporalWalk x n y m) : p.arcs.length = p.length := by
  cases p <;> grind

/-- The list of edges of a walk has as many entries as the walk's length. -/
@[simp]
theorem length_edges (p : G.TemporalWalk x n y m) : p.edges.length = p.length := by
  simp [edges]

/-- A walk traverses at most as many distinct edges as its length. -/
theorem ncard_setOf_mem_edges_le (p : G.TemporalWalk x n y m) :
    {e | e ∈ p.edges}.ncard ≤ p.length := by
  classical
  have : {e | e ∈ p.edges} = ↑p.edges.toFinset := by ext; simp
  rw [this, Set.ncard_coe_finset, ← length_edges]
  exact List.toFinset_card_le _

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
  | nil => grind only [arcs, ← List.not_mem_nil]
  | ofNonempty p => exact p.adj_of_mem_arcs

/-- Every edge of a walk is an edge of the graph. -/
@[grind →]
theorem edges_subset_edgeSet (p : G.TemporalWalk x n y m) :
    ∀ ⦃e⦄, e ∈ p.edges → e ∈ G.edgeSet := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he
  exact ⟨a.1, a.2.1, rfl, (p.adj_of_mem_arcs a ha).1⟩

/-- If the edges of a walk lie in a symmetric graph `G'`, so do its arcs. -/
@[grind →]
theorem adj_of_edges_subset {G' : TemporalGraph V} [G'.IsSymm] (p : G.TemporalWalk x n y m)
    (h₀ : ∀ e ∈ p.edges, e ∈ G'.edgeSet) : ∀ a ∈ p.arcs, G'.Adj a.1 a.2.1 a.2.2 := by
  intro a ha
  exact G'.mem_edgeSet.1 (h₀ _ (List.mem_map.2 ⟨a, ha, rfl⟩))

end API

end TemporalWalk

namespace NonemptyTemporalWalk

/-- Automatic coercion of a `NonemptyTemporalWalk` to a `TemporalWalk`, since it is never empty. -/
instance {x y : V} {n m : ℕ} : Coe (G.NonemptyTemporalWalk x n y m) (G.TemporalWalk x n y m) where
  coe  p := TemporalWalk.ofNonempty p

/-- Seen as a `TemporalWalk`, a nonempty walk keeps its strictness. -/
@[simp, grind =]
theorem isStrict_ofNonempty {x y : V} {n m : ℕ} (p : G.NonemptyTemporalWalk x n y m) :
    (TemporalWalk.ofNonempty p).IsStrict ↔ p.IsStrict :=
  Iff.rfl

/-- In a proper symmetric graph, every non-strict walk can be shortened into a strict one with the
same endpoints, starting no earlier and ending no later. Two consecutive arcs `w → y → z` at the
same time are, by properness of the symmetric graph, the same edge crossed back and forth
(`w = z`): the shortening deletes such round trips, and may leave the empty walk. -/
theorem exists_isStrict [G.IsSymm] {x y : V} {n m : ℕ} (h₀ : G.IsProper)
    (p : G.NonemptyTemporalWalk x n y m) :
    ∃ n' m', ∃ q : G.TemporalWalk x n' y m', q.IsStrict ∧ n ≤ n' ∧ m' ≤ m := by
  induction p with
  | single h => exact ⟨_, _, .ofNonempty (.single h), trivial, le_rfl, le_rfl⟩
  | @step y z n m k p h h₁ ih =>
    obtain ⟨n', m', q, hq, hn, hm⟩ := ih
    cases q with
    | nil => exact ⟨k, k, .ofNonempty (.single h), trivial, p.nondecreasing_time.trans h₁, le_rfl⟩
    | ofNonempty q =>
      by_cases hlt : m' < k
      · exact ⟨n', k, .ofNonempty (q.step h hlt.le), ⟨hlt, hq⟩, hn, le_rfl⟩
      obtain rfl : m' = k := by omega
      cases q with
      | single h₂ =>
        -- the walk is `x → y → z` at a single time: a round trip, so `z = x`
        obtain rfl := h₀ h₂.symm h
        exact ⟨n', n', .nil, trivial, hn, le_rfl⟩
      | step q h₂ h₃ =>
        -- the last two arcs `w → y → z` share their time: a round trip, so `z = w`
        obtain rfl := h₀ h₂.symm h
        exact ⟨n', _, .ofNonempty q, hq.2, hn, h₃⟩

end NonemptyTemporalWalk

end TemporalGraph
