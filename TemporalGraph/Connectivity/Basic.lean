/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.TemporalWalk

/-!
# Reachability and Connectivity

Defines reachability in temporal graphs: vertex `y` is reachable from `x` if there exists
a temporal walk from `x` to `y`. Note that `Reachable` is **directional even for symmetric
graphs**, since walk times must be non-decreasing. Walks are *non-strict*; `StrictReachable` asks
for a strict walk, and `reachable_iff_strictReachable` shows that the two notions coincide in a
proper symmetric graph.

## Main definitions
* `Reachable` : Existence of a temporal walk between two vertices
* `ReachableWithin` : `x` reaches `y` by a walk (possibly empty) leaving at a time `≥ a` and
  arriving at a time `≤ b`; `ReachableBefore` (window `[0, b]`) and `ReachableAfter` (only the
  departure bounded) are its one-sided variants
* `StrictReachable` : Existence of a strict temporal walk between two vertices
* `TemporallyConnected` : every pair of vertices of a given set `S` is mutually reachable (takes
  `S` as an explicit argument, mirroring `IsClique`)
* `TemporallyConnectedGraph` : the whole-graph shorthand `TemporallyConnected Set.univ`; on a
  subgraph `H`, the subgraph-level shorthand `H.TemporallyConnectedSubgraph` (`Connectivity/
  Subgraph.lean`) asks only `H.verts` to be connected, mirroring `IsCliqueGraph`/`IsCliqueSubgraph`

Spanner notions (`Subgraph.IsSpanner`, `Subgraph.IsSpannerOf` and `Subgraph.IsTCSpanner`) are
defined at the `Subgraph` level, in `Connectivity/Subgraph.lean`.

## Main results
* `Reachable.refl`, `StrictReachable.refl` : Every vertex reaches itself
* `ReachableWithin.refl`, `ReachableWithin.step`, `ReachableWithin.cons` : empty walk, extension
  by one arc at the end, and at the start
* `ReachableWithin.mono`, `ReachableWithin.mono_window` : monotone along `≤` and in the window
* `ReachableWithin.reachable`, `reachable_iff_exists_reachableWithin` : link with `Reachable`
* `StrictReachable.reachable` : Strict reachability implies reachability
* `Reachable.mono`, `StrictReachable.mono` : Reachability is monotone along `≤`
* `reachable_iff_strictReachable` : in a proper symmetric graph, strict and non-strict
  reachability coincide
* `temporallyConnected_of_isClique` : Cliques are temporally connected
* `reachable_of_earliestEdge`, `reachable_of_latestEdge` : Reachability preservation lemmas
* `reachable_of_extended_earliestEdge`, `reachable_of_extended_latestEdge` : Variants of these
  lemmas, starting from a vertex `z` joined to the neighbor by an edge at a compatible time
-/

@[expose] public section

universe u
variable {V : Type u}

namespace TemporalGraph

/-- `y` is *reachable* from `x`: some (non-strict) temporal walk goes from `x` to `y`. -/
def Reachable (G : TemporalGraph V) (x y : V) : Prop :=
  ∃ n m : ℕ, Nonempty (G.TemporalWalk x n y m)

/-- The type of `NonemptyTemporalWalk` is `Nonempty`. -/
theorem NonemptyTemporalWalk.reachable {G : TemporalGraph V} {x y : V} {n m : ℕ}
    (p : G.NonemptyTemporalWalk x n y m) : G.Reachable x y :=
  ⟨n, m, ⟨.ofNonempty p⟩⟩

/-- Every vertex reaches itself, via the empty walk. -/
@[refl]
theorem Reachable.refl {G : TemporalGraph V} (x : V) : G.Reachable x x := by
  use 0, 0, TemporalWalk.nil

/-- `Reachable` restated with `Set.univ` nonemptiness standing in for the type being `Nonempty`
(the name and form of Mathlib's `SimpleGraph.reachable_iff_nonempty_univ`). -/
theorem reachable_iff_nonempty_univ {G : TemporalGraph V} {x y : V} :
    G.Reachable x y ↔ ∃ n m : ℕ, (Set.univ : Set (G.TemporalWalk x n y m)).Nonempty := by
  unfold Reachable
  apply Iff.intro
  · intro ⟨n, ⟨m, ⟨p⟩⟩⟩
    exact ⟨n, ⟨m, ⟨p, trivial⟩⟩⟩
  · intro ⟨n, ⟨m, ⟨p, _⟩⟩⟩
    exact ⟨n, ⟨m, ⟨p⟩⟩⟩

/-- Reachability is monotone along `≤`: every pair reachable in `G` stays reachable in a graph
`G'` that has all of `G`'s arcs. -/
theorem Reachable.mono {G G' : TemporalGraph V} (h : G ≤ G') {x y : V} :
    G.Reachable x y → G'.Reachable x y := by
  rintro ⟨n, m, ⟨w⟩⟩
  exact ⟨n, m, ⟨w.mapLe h⟩⟩

section ReachableWithin

variable {G G' : TemporalGraph V} {x y z : V} {a a' b b' k : ℕ}

/-- `x` reaches `y` within the time window `[a, b]`: some temporal walk, possibly empty, leaves `x`
at a time `≥ a` and arrives at `y` at a time `≤ b`. -/
def ReachableWithin (G : TemporalGraph V) (x y : V) (a b : ℕ) : Prop :=
  ∃ n m : ℕ, a ≤ n ∧ m ≤ b ∧ Nonempty (G.TemporalWalk x n y m)

/-- `x` reaches `y` by time `b`: the window `[0, b]`, only the arrival is bounded. -/
abbrev ReachableBefore (G : TemporalGraph V) (x y : V) (b : ℕ) : Prop :=
  G.ReachableWithin x y 0 b

/-- `x` reaches `y` from time `a` on: only the departure is bounded. -/
abbrev ReachableAfter (G : TemporalGraph V) (x y : V) (a : ℕ) : Prop :=
  ∃ b, G.ReachableWithin x y a b

/-- Every vertex reaches itself within any nonempty window, via the empty walk at time `a`. -/
theorem ReachableWithin.refl (x : V) (h₀ : a ≤ b) : G.ReachableWithin x x a b :=
  ⟨a, a, le_rfl, h₀, ⟨.nil⟩⟩

/-- Extend a window-bounded walk by one arc at the end, at a time `k ≥ b`. -/
theorem ReachableWithin.step (h₀ : G.ReachableWithin x y a b) (h₁ : G.Adj y z k) (h₂ : b ≤ k) :
    G.ReachableWithin x z a k := by
  obtain ⟨n, m, hn, hm, ⟨p⟩⟩ := h₀
  cases p with
  | nil => exact ⟨k, k, by omega, le_rfl, ⟨.ofNonempty (.single h₁)⟩⟩
  | ofNonempty p => exact ⟨n, k, hn, le_rfl, ⟨.ofNonempty (p.step h₁ (by omega))⟩⟩

/-- Prepend one arc, at a time `k ≥ a`, to a walk that leaves `y` at time `≥ k`. -/
theorem ReachableWithin.cons (h₀ : G.Adj x y k) (h₁ : a ≤ k) (h₂ : G.ReachableWithin y z k b) :
    G.ReachableWithin x z a b := by
  obtain ⟨n, m, hn, hm, ⟨p⟩⟩ := h₂
  cases p with
  | nil => exact ⟨k, k, h₁, by omega, ⟨.ofNonempty (.single h₀)⟩⟩
  | ofNonempty p => exact ⟨k, m, h₁, hm, ⟨.ofNonempty (p.prepend h₀ hn)⟩⟩

/-- Window reachability is monotone along `≤`. -/
theorem ReachableWithin.mono (h₀ : G ≤ G') (h₁ : G.ReachableWithin x y a b) :
    G'.ReachableWithin x y a b := by
  obtain ⟨n, m, hn, hm, ⟨p⟩⟩ := h₁
  exact ⟨n, m, hn, hm, ⟨p.mapLe h₀⟩⟩

/-- A larger window keeps the reachability. -/
theorem ReachableWithin.mono_window (h₀ : G.ReachableWithin x y a b) (h₁ : a' ≤ a) (h₂ : b ≤ b') :
    G.ReachableWithin x y a' b' := by
  obtain ⟨n, m, hn, hm, hp⟩ := h₀
  exact ⟨n, m, h₁.trans hn, hm.trans h₂, hp⟩

/-- Reachability within a window implies reachability: forget the window. -/
@[grind →]
theorem ReachableWithin.reachable (h₀ : G.ReachableWithin x y a b) : G.Reachable x y :=
  let ⟨n, m, _, _, hp⟩ := h₀
  ⟨n, m, hp⟩

/-- Reachability is reachability within some window. -/
theorem reachable_iff_exists_reachableWithin :
    G.Reachable x y ↔ ∃ a b, G.ReachableWithin x y a b :=
  ⟨fun ⟨n, m, hp⟩ ↦ ⟨n, m, n, m, le_rfl, le_rfl, hp⟩, fun ⟨_, _, h⟩ ↦ h.reachable⟩

end ReachableWithin

/-- `y` is *strictly reachable* from `x`: some strict temporal walk, whose times increase strictly
from each arc to the next, goes from `x` to `y`. -/
def StrictReachable (G : TemporalGraph V) (x y : V) : Prop :=
  ∃ n m : ℕ, ∃ p : G.TemporalWalk x n y m, p.IsStrict

/-- Every vertex strictly reaches itself, via the empty walk. -/
theorem StrictReachable.refl {G : TemporalGraph V} (x : V) : G.StrictReachable x x :=
  ⟨0, 0, .nil, trivial⟩

/-- Strict reachability implies reachability: forget that the walk is strict. -/
theorem StrictReachable.reachable {G : TemporalGraph V} {x y : V} :
    G.StrictReachable x y → G.Reachable x y := by
  rintro ⟨n, m, p, -⟩
  exact ⟨n, m, ⟨p⟩⟩

/-- Strict reachability is monotone along `≤`: mapping a walk keeps it strict. -/
theorem StrictReachable.mono {G G' : TemporalGraph V} (h : G ≤ G') {x y : V} :
    G.StrictReachable x y → G'.StrictReachable x y := by
  rintro ⟨n, m, p, hp⟩
  exact ⟨n, m, p.mapLe h, (TemporalWalk.isStrict_mapLe h p).mpr hp⟩

/-- In a proper symmetric temporal graph, reachability and strict reachability coincide. Walks
themselves differ: crossing an edge and immediately crossing it back at the same time is a
non-strict walk that is not strict, but `NonemptyTemporalWalk.exists_isStrict` deletes such round
trips. Symmetry is needed: the oriented, proper graph with the two arcs `a → y` and `y → z`, both
at time `1`, lets `a` reach `z`, but not strictly. -/
theorem reachable_iff_strictReachable {G : TemporalGraph V} [G.IsSymm] {x y : V}
    (h₀ : G.IsProper) : G.Reachable x y ↔ G.StrictReachable x y := by
  refine ⟨?_, StrictReachable.reachable⟩
  rintro ⟨n, m, ⟨p⟩⟩
  cases p with
  | nil => exact StrictReachable.refl x
  | ofNonempty p =>
    obtain ⟨n', m', q, hq, -, -⟩ := p.exists_isStrict h₀
    exact ⟨n', m', q, hq⟩

/-- `S` is temporally connected in `G`: every vertex of `S` reaches every vertex of `S`. -/
abbrev TemporallyConnected (G : TemporalGraph V) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, G.Reachable x y

/-- `G` is temporally connected. Shorthand for `G.TemporallyConnected Set.univ`. On a subgraph
`H`, use `H.TemporallyConnectedSubgraph`: the inherited `H.TemporallyConnectedGraph` asks all of
`V` to be connected. -/
abbrev TemporallyConnectedGraph (G : TemporalGraph V) : Prop := G.TemporallyConnected Set.univ

/-- A clique on `S` is temporally connected on `S`: distinct vertices of `S` are joined by the
clique's single edge, and every vertex reaches itself. -/
theorem temporallyConnected_of_isClique (G : TemporalGraph V) {S : Set V} :
    G.IsClique S → G.TemporallyConnected S := by
  unfold IsClique TemporallyConnected
  intro h x hx y hy
  by_cases hdiff : x ≠ y
  · have ⟨n, h'⟩ := h hx hy hdiff
    exact NonemptyTemporalWalk.reachable (NonemptyTemporalWalk.single h')
  · simp_all [Reachable.refl]

/-- If `n` is the time of `x`'s earliest edge, to `y`, then anything reachable from `x` is also
reachable from `y`: prepend the reversed edge (time `n`, necessarily `≤` any walk out of `x`) to
the witnessing walk. -/
lemma reachable_of_earliestEdge {x y : V} {n : ℕ} {G : TemporalGraph V} [G.IsSymm]
    (h : G.EarliestEdge x y n) :
    ∀ z : V, G.Reachable x z → G.Reachable y z := by
  rw [EarliestEdge] at h
  intro _ ⟨m, _, ⟨p⟩⟩
  cases p with
  | nil =>
    exact (NonemptyTemporalWalk.single h.left.symm).reachable
  | ofNonempty p =>
    have hst : n ≤ m := EarliestEdge.le_start h p
    exact NonemptyTemporalWalk.reachable (p.prepend h.left.symm hst)

/-- A variant of `reachable_of_earliestEdge`: given also an edge `z -m-> y` with `m ≤ n`, anything
reachable from `x` is also reachable from `z`, via `z -m-> y -n-> x` followed by the witnessing
walk. -/
lemma reachable_of_extended_earliestEdge {x y z : V} {n m : ℕ} {G : TemporalGraph V} [G.IsSymm]
    (h₀ : G.EarliestEdge x y n)
    (h₁ : G.Adj z y m)
    (h₂ : m ≤ n) :
    ∀ a : V, G.Reachable x a → G.Reachable z a := by
  intro _ ⟨k, _, ⟨p⟩⟩
  let p' : NonemptyTemporalWalk z m x n :=
    NonemptyTemporalWalk.single h₁ |>.step h₀.left.symm h₂
  cases p with
  | nil =>
      exact p'.reachable
  | ofNonempty p =>
    have h : n ≤ k := h₀.le_start p
    exact NonemptyTemporalWalk.reachable (p'.append p h)

/-- If `n` is the time of `x`'s latest edge, to `y`, then anything that reaches `x` also reaches
`y`: append the edge (time `n`, necessarily `≥` any walk into `x`) to the witnessing walk. -/
lemma reachable_of_latestEdge {x y : V} {n : ℕ} {G : TemporalGraph V} [G.IsSymm]
    (h : G.LatestEdge x y n) :
    ∀ z : V, G.Reachable z x → G.Reachable z y := by
  intro _ ⟨_, m, ⟨p⟩⟩
  cases p with
  | nil =>
    exact NonemptyTemporalWalk.reachable (NonemptyTemporalWalk.single h.left)
  | ofNonempty p =>
    have het : m ≤ n := h.end_le p
    exact NonemptyTemporalWalk.reachable (p.step h.left het)

/-- A variant of `reachable_of_latestEdge`: given also an edge `y -m-> z` with `n ≤ m`, anything
that reaches `x` also reaches `z`, by appending `x -n-> y -m-> z` to the witnessing walk. -/
lemma reachable_of_extended_latestEdge {x y z : V} {n m : ℕ} {G : TemporalGraph V} [G.IsSymm]
    (h₀ : G.LatestEdge x y n)
    (h₁ : G.Adj y z m)
    (h₂ : n ≤ m) :
    ∀ a : V, G.Reachable a x → G.Reachable a z := by
  intro _ ⟨_, k, ⟨p⟩⟩
  let p' : NonemptyTemporalWalk x n z m := NonemptyTemporalWalk.single h₀.left |>.step h₁ h₂
  cases p with
  | nil =>
      exact p'.reachable
  | ofNonempty p =>
    have h : k ≤ n := h₀.end_le p
    exact NonemptyTemporalWalk.reachable (p.append p' h)

end TemporalGraph
