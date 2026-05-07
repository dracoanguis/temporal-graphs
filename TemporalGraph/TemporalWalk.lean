/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.NonemptyTemporalWalk

universe u

variable {V : Type u} {G : LooplessTemporalGraph V}

namespace LooplessTemporalGraph

/-- We define a Non-strict TemporalWalk, meaning multiple edges can be crossed at a given time. -/
inductive TemporalWalk : V → ℕ → V → ℕ → Type u
  | Empty {x : V} {n : ℕ} : TemporalWalk x n x n
  | Nonempty {x y : V} {n m : ℕ} (p : G.NonemptyTemporalWalk x n y m) : TemporalWalk x n y m
  deriving DecidableEq

def TemporalWalkSet (x y : V) :
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

/-- The `darts` of a TemporalWalk is the list of darts (edge with a direction) it visits in
order. -/
def darts {x y : V} {n m : ℕ} : G.TemporalWalk x n y m → List (V × V × ℕ)
  | Empty => []
  | Nonempty p => p.darts

lemma time_monotonicity {x y : V} {n m : ℕ} (tw : G.TemporalWalk x n y m) : n ≤ m := by
  cases tw with
  | Empty => trivial
  | Nonempty p => exact p.time_monotonicity

end TemporalWalk

namespace NonemptyTemporalWalk

-- Auto coercion to a TemporalWalk since they are never empty
instance {x y : V} {n m : ℕ} : Coe (G.NonemptyTemporalWalk x n y m) (G.TemporalWalk x n y m) where
  coe  p := TemporalWalk.Nonempty p

end NonemptyTemporalWalk

end LooplessTemporalGraph
