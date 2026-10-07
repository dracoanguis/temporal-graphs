/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Basic

/-!
# Nonempty Temporal Walks

Defines `NonemptyTemporalWalk`, an inductive type for temporal walks that are guaranteed
to contain at least one edge. Times must be non-decreasing along the walk (*non-strict* walks);
`IsStrict` selects the walks whose times increase strictly.

## Main definitions
* `NonemptyTemporalWalk` : A walk with at least one edge and non-decreasing times
* `length` : The number of edges in a walk
* `support` : The list of vertices visited
* `arcs` : The list of directed edges (as triples `V × V × ℕ`)
* `append` : Concatenate two compatible walks
* `prepend` : Add an edge at the start of a walk
* `mapLe` : Transport a walk along a spanning-subgraph inclusion `G ≤ G'`
* `IsStrict` : the walk's times increase strictly from each arc to the next

## Main results
* `nondecreasing_time` : Times are non-decreasing along a walk
* `exists_adj_fst` : The first vertex of a walk has an outgoing arc
* `exists_adj_snd` : The last vertex of a walk has an incoming arc
* `length_append`, `arcs_append` : Concatenation lemmas for walk length and arcs
* `length_mapLe`, `support_mapLe`, `arcs_mapLe` : Mapping preserves length, support and arcs
* `mapLe_append`, `mapLe_mapLe` : Composition lemmas for `mapLe`
* `isStrict_mapLe`, `isStrict_append` : Strictness under mapping and concatenation
* `start_mem_support`, `end_mem_support` : Walk endpoints belong to the support
* `adj_of_mem_arcs` : Every arc in a walk is an edge within the time bounds
-/

@[expose] public section

universe u

namespace TemporalGraph

variable {V : Type u} {G : TemporalGraph V}

/-- A nonempty *non-strict* temporal walk from `x` at time `n` to `y` at time `m`: times are only
required to be non-decreasing along the walk. `IsStrict` singles out the strict ones. -/
inductive NonemptyTemporalWalk : V → ℕ → V → ℕ → Type u
  | single {x y : V} {n : ℕ} (h: G.Adj x y n) : NonemptyTemporalWalk x n y n
  | step {x y z : V} {n m k : ℕ}
    (p : NonemptyTemporalWalk x n y m) (h : G.Adj y z k) (h' : m ≤ k) :
    NonemptyTemporalWalk x n z k
  deriving DecidableEq

namespace NonemptyTemporalWalk

/-- The length of a NonemptyTemporalWalk is the number of edges along it. -/
@[grind =]
def length {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → ℕ
  | single _ => 1
  | step p _ _ => 1 + p.length

/-- The `support` of a NonemptyTemporalWalk is the list of vertices it visits, stored from the end
vertex back to the start vertex. -/
@[grind =]
def support {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → List V
  | single _ => y :: [x]
  | step p _ _ => y :: p.support

-- Arcs
/-- The `arcs` of a NonemptyTemporalWalk is the list of arcs (edge with a direction) it traverses,
stored last arc first. -/
@[grind =]
def arcs {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → List (V × V × ℕ)
  | @single _ _ x y n _ => [⟨x ,⟨y, n⟩⟩]
  | @step _ _ _ y z _ _ k p _ _ => ⟨y ,⟨ z, k⟩⟩ :: p.arcs

/-- A walk is *strict* when the time increases strictly from each arc to the next. A
`NonemptyTemporalWalk` is only required to be non-decreasing; the two notions differ even in a
proper symmetric graph, where crossing an edge and immediately crossing it back at the same time
is a non-strict walk but not a strict one. -/
@[grind =]
def IsStrict {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → Prop
  | single _ => True
  | @step _ _ _ _ _ _ m k p _ _ => m < k ∧ p.IsStrict

/-- Concatenate two compatible NonemptyTemporalWalks. -/
@[grind =]
def append {x y z : V} {n m k l}
    (p : G.NonemptyTemporalWalk x n y m) (ext : G.NonemptyTemporalWalk y k z l)
    (h : m ≤ k) :
    G.NonemptyTemporalWalk x n z l :=
  match ext with
  | single h_edge => p.step h_edge h
  | step p' h_edge h_ord' => step (append p p' h) h_edge h_ord'

/-- The reversed version of `NonemptyTemporalWalk.step`, concatening an edge at the start of a
walk. -/
def prepend {x y z : V} {n m k : ℕ}
    (p : G.NonemptyTemporalWalk x n y m) (h : G.Adj z x k) (h' : k ≤ n) :
    G.NonemptyTemporalWalk z k y m :=
  append (single h) p h'

/-- Map a walk along `G ≤ G'`: every arc of `G` is an arc of `G'`, so a walk of `G` is a walk of
`G'`, unchanged in its vertices and times. -/
@[grind =]
protected def mapLe {G' : TemporalGraph V} (h : G ≤ G') {x y : V} {n m : ℕ} :
    G.NonemptyTemporalWalk x n y m → G'.NonemptyTemporalWalk x n y m
  | single h' => single (h h')
  | step p h' h'' => step (p.mapLe h) (h h') h''

/-- Times are non-decreasing along a walk: `n ≤ m`. -/
lemma nondecreasing_time {x y : V} {n m : ℕ} (tw : G.NonemptyTemporalWalk x n y m) : n ≤ m := by
  induction tw with
  | single h => rfl
  | step h p h' ih => exact le_trans ih h'

/-- The first vertex of a walk has an outgoing arc, found by recursing to the walk's innermost
edge. -/
lemma exists_adj_fst {x y : V} {n m : ℕ} (tw : G.NonemptyTemporalWalk x n y m) :
    ∃ z j, G.Adj x z j := by
  induction tw with
  | single h => exact ⟨_, _, h⟩
  | step _ _ _ ih => exact ih

/-- The last vertex of a walk has an incoming arc: its outermost edge. -/
lemma exists_adj_snd {x y : V} {n m : ℕ} (tw : G.NonemptyTemporalWalk x n y m) :
    ∃ z j, G.Adj z y j := by
  cases tw with
  | single h => exact ⟨_, _, h⟩
  | step _ h _ => exact ⟨_, _, h⟩

/-- The earliest edge out of a walk's start vertex occurs no later than the walk's start time. -/
lemma EarliestEdge.time_bound_of_edge {x y z : V} {n m k : ℕ}
    (tw : G.NonemptyTemporalWalk x n y m) (h : G.EarliestEdge x z k) :
    k ≤ n := by
  induction tw with
  | single h' => grind only [= EarliestEdge.eq_1]
  |step _ _ _ hi => exact hi

/-- For a symmetric graph, the latest edge out of a walk's end vertex occurs no earlier than the
walk's end time. -/
lemma LatestEdge.time_bound_of_edge {x y z : V} {n m k : ℕ} [G.IsSymm]
    (tw : G.NonemptyTemporalWalk x n y m) (h : G.LatestEdge y z k) :
    m ≤ k := by
  cases tw with
  | single h' => grind only [→ adj_symm, = LatestEdge.eq_1]
  | step _ h' _ => exact h.right _ _ h'.symm


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

/-- Mapping a walk along `G ≤ G'` preserves strictness. -/
@[simp, grind =]
theorem isStrict_mapLe {G' : TemporalGraph V} (h₀ : G ≤ G') (p : G.NonemptyTemporalWalk x n y m) :
    (p.mapLe h₀).IsStrict ↔ p.IsStrict := by
  induction p <;> grind

/-- A concatenation is strict iff both walks are, and the junction is strict. -/
@[simp, grind =]
theorem isStrict_append (p : G.NonemptyTemporalWalk x n y m) (q : G.NonemptyTemporalWalk y k z l)
    (h₀ : m ≤ k) : (p.append q h₀).IsStrict ↔ p.IsStrict ∧ q.IsStrict ∧ m < k := by
  induction q <;> grind

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
  | single h => grind only [arcs, = List.mem_cons, ← List.not_mem_nil]
  | step p h h' ih => have := p.nondecreasing_time; grind only [arcs, = List.mem_cons]

end API

end NonemptyTemporalWalk

end TemporalGraph
