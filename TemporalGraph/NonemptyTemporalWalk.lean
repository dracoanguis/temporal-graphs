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
* `mapLe` : Transport a walk along a spanning-subgraph inclusion `G ≤ G'`

## Main results
* `nondecreasing_time` : Times are non-decreasing along a walk
* `exists_adj_fst` : The first vertex of a walk has an outgoing arc
* `exists_adj_snd` : The last vertex of a walk has an incoming arc
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
@[grind =]
def length {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → ℕ
  | Single _ => 1
  | Step p _ _ => 1 + p.length

/-- The `support` of a NonemptyTemporalWalk is the list of vertices it visits in order. -/
@[grind =]
def support {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → List V
  | Single _ => y :: [x]
  | Step p _ _ => y :: p.support

-- Arcs
/-- The `arcs` of a NonemptyTemporalWalk is the list of arcs (edge with a direction) it visits in
order. -/
@[grind =]
def arcs {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → List (V × V × ℕ)
  | @Single _ _ x y n _ => [⟨x ,⟨y, n⟩⟩]
  | @Step _ _ _ y z _ _ k p _ _ => ⟨y ,⟨ z, k⟩⟩ :: p.arcs

/-- Concatenate two compatible NonemptyTemporalWalks. -/
@[grind =]
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

/-- Map a walk along `G ≤ G'`: every arc of `G` is an arc of `G'`, so a walk of `G` is a walk of
`G'`, unchanged in its vertices and times. -/
@[grind =]
protected def mapLe {G' : TemporalGraph V} (h : G ≤ G') {x y : V} {n m : ℕ} :
    G.NonemptyTemporalWalk x n y m → G'.NonemptyTemporalWalk x n y m
  | Single h' => Single (h h')
  | Step p h' h'' => Step (p.mapLe h) (h h') h''

/-- Times are non-decreasing along a walk: `n ≤ m`. -/
@[simp]
lemma nondecreasing_time {x y : V} {n m : ℕ} (tw : G.NonemptyTemporalWalk x n y m) : n ≤ m := by
  induction tw with
  | Single h => rfl
  | Step h p h' ih => exact le_trans ih h'

/-- The first vertex of a walk has an outgoing arc, found by recursing to the walk's innermost
edge. -/
lemma exists_adj_fst {x y : V} {n m : ℕ} (tw : G.NonemptyTemporalWalk x n y m) :
    ∃ z j, G.Adj x z j := by
  induction tw with
  | Single h => exact ⟨_, _, h⟩
  | Step _ _ _ ih => exact ih

/-- The last vertex of a walk has an incoming arc: its outermost edge. -/
lemma exists_adj_snd {x y : V} {n m : ℕ} (tw : G.NonemptyTemporalWalk x n y m) :
    ∃ z j, G.Adj z y j := by
  cases tw with
  | Single h => exact ⟨_, _, h⟩
  | Step _ h _ => exact ⟨_, _, h⟩

/-- The earliest edge out of a walk's start vertex occurs no later than the walk's start time. -/
lemma EarliestEdge.time_bound_of_edge {x y z : V} {n m k : ℕ}
    (tw : G.NonemptyTemporalWalk x n y m) (h : G.EarliestEdge x z k) :
    k ≤ n := by
  induction tw with
  | Single h' => grind only [= EarliestEdge.eq_1]
  |Step _ _ _ hi => exact hi

/-- For a symmetric graph, the latest edge out of a walk's end vertex occurs no earlier than the
walk's end time. -/
lemma LatestEdge.time_bound_of_edge {x y z : V} {n m k : ℕ} [G.IsSymm]
    (tw : G.NonemptyTemporalWalk x n y m) (h : G.LatestEdge y z k) :
    m ≤ k := by
  cases tw with
  | Single h' => grind only [→ adj_symm, = LatestEdge.eq_1]
  | Step _ h' _ => exact h.right _ _ h'.symm


section API

variable {x y z : V} {n m k l : ℕ}

/-- The length of a concatenation is the sum of the lengths. -/
@[simp, grind =]
theorem length_append (p : G.NonemptyTemporalWalk x n y m) (q : G.NonemptyTemporalWalk y k z l)
    (h₀ : m ≤ k) : (p.append q h₀).length = p.length + q.length := by
  induction q <;> grind

/-- The arcs of a concatenation are those of the second walk followed by those of the first
(the lists are stored last arc first). -/
@[simp, grind =]
theorem arcs_append (p : G.NonemptyTemporalWalk x n y m) (q : G.NonemptyTemporalWalk y k z l)
    (h₀ : m ≤ k) : (p.append q h₀).arcs = q.arcs ++ p.arcs := by
  induction q <;> grind

/-- Mapping a walk along `G ≤ G'` preserves its length. -/
@[simp, grind =]
theorem length_mapLe {G' : TemporalGraph V} (h₀ : G ≤ G') (p : G.NonemptyTemporalWalk x n y m) :
    (p.mapLe h₀).length = p.length := by
  induction p <;> grind

/-- Mapping a walk along `G ≤ G'` preserves its support. -/
@[simp, grind =]
theorem support_mapLe {G' : TemporalGraph V} (h₀ : G ≤ G')
    (p : G.NonemptyTemporalWalk x n y m) : (p.mapLe h₀).support = p.support := by
  induction p <;> grind

/-- Mapping a walk along `G ≤ G'` preserves its arcs. -/
@[simp, grind =]
theorem arcs_mapLe {G' : TemporalGraph V} (h₀ : G ≤ G') (p : G.NonemptyTemporalWalk x n y m) :
    (p.mapLe h₀).arcs = p.arcs := by
  induction p <;> grind

/-- Mapping a walk along `G ≤ G'` commutes with concatenation. -/
theorem mapLe_append {G' : TemporalGraph V} (h₀ : G ≤ G') (p : G.NonemptyTemporalWalk x n y m)
    (q : G.NonemptyTemporalWalk y k z l) (h₁ : m ≤ k) :
    (p.append q h₁).mapLe h₀ = (p.mapLe h₀).append (q.mapLe h₀) h₁ := by
  induction q <;> grind

/-- Mapping a walk along `G ≤ G'` then `G' ≤ G''` is mapping it along `G ≤ G''`. -/
@[simp]
theorem mapLe_mapLe {G' G'' : TemporalGraph V} (h₀ : G ≤ G') (h₁ : G' ≤ G'')
    (p : G.NonemptyTemporalWalk x n y m) :
    (p.mapLe h₀).mapLe h₁ = p.mapLe (fun h ↦ h₁ (h₀ h)) := by
  induction p <;> grind

/-- The start vertex of a walk belongs to its support. -/
@[grind .]
theorem start_mem_support (p : G.NonemptyTemporalWalk x n y m) : x ∈ p.support := by
  induction p <;> grind

/-- The end vertex of a walk belongs to its support. -/
@[grind .]
theorem end_mem_support (p : G.NonemptyTemporalWalk x n y m) : y ∈ p.support := by
  cases p <;> grind

/-- Every arc of a walk is an edge of the graph, at a time between the start and end times. -/
theorem adj_of_mem_arcs (p : G.NonemptyTemporalWalk x n y m) :
    ∀ a ∈ p.arcs, G.Adj a.1 a.2.1 a.2.2 ∧ n ≤ a.2.2 ∧ a.2.2 ≤ m := by
  induction p with
  | Single h => grind only [arcs, = List.mem_cons, ← List.not_mem_nil]
  | Step p h h' ih => have := p.nondecreasing_time; grind only [arcs, = List.mem_cons]

end API

end NonemptyTemporalWalk

end TemporalGraph
