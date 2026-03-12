/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.SubTempGraph

universe u

variable {V : Type u}

namespace SimpleTemporalGraph

def EarliestNeigbhor {G : SimpleTemporalGraph V} (x y : V) : Prop
:= ∃ n : ℕ, G.EarliestEdge x y n

def LatestNeighbor {G : SimpleTemporalGraph V} (x y : V) : Prop
:= ∃ n, G.LatestEdge x y n

namespace SubTempGraph

variable {G : SimpleTemporalGraph V}

def EarliestEdge (H : SubTempGraph G) (x y : V) (n : ℕ) : Prop
:= H.Adj x y n ∧ ∀ (z : V) (m : ℕ), H.Adj x z m → n ≤ m

def LatestEdge (H : SubTempGraph G) (x y : V) (n : ℕ) : Prop
:= H.Adj x y n ∧ ∀ (z : V) (m : ℕ), H.Adj x z m → m ≤ n

def EarliestNeighbor {H : SubTempGraph G} (x y : V) : Prop
:= ∃ n, H.EarliestEdge x y n

def LatestNeighbor {H : SubTempGraph G} (x y : V) : Prop
:= ∃ n, H.LatestEdge x y n

-- lemma earliestEdge_exists {H : SubTempGraph G} {x y : V} {n : ℕ}
-- (h : H.Adj x y n)
-- : ∃ (z : V) (m : ℕ), H.EarliestEdge x z m
-- := by
--   simp only [EarliestEdge]
--   by_contra h'
--   conv at h' =>
--     simp only [not_exists] ;
--     rhs ; rhs ; rw [not_and_or] ;
--     rhs ; simp only [not_forall, exists_prop, not_le] ;

--   have h'' := h' y n
--   simp only [h, not_true_eq_false, false_or] at h''
--   have ⟨w, s, hee⟩ := h''

  -- by_cases hee : ∀ (w : V) (t' : ℕ), G'.Adj u w t' → t ≤ t'
  -- · constructor ; assumption' ; use t
  -- · push_neg at hee
  --   have ⟨w, s, hee'⟩ := hee
  --   use w, s
  --   constructor
  --   · exact hee'.left
  --   ·

lemma latestEdge_exists {H : SubTempGraph G} {x y : V} {n : ℕ}
(h : H.Adj x y n)
: ∃ (z : V) (m : ℕ), H.LatestEdge x z m := by sorry

def IsClique (H : SubTempGraph G) : Prop
:= ∀ (x y : H.Verts), x ≠ y → ∃ n, H.Adj x y n

def IsProper (H : SubTempGraph G) : Prop
:= ∀ (x y z : V) (n : ℕ), H.Adj x y n ∧ H.Adj x z n → y=z

-- From SimpleGraph.Subgraph.IsMatching
def IsMatching (M : SubTempGraph G) : Prop
:= ∀ ⦃v : V⦄, v ∈ M.Verts → ∃! w , ∃ t, M.Adj v w t

-- From SimpleGraph.Subgraph.IsPerfectMatching
def IsPerfectMatching (M : SubTempGraph G)
:= M.IsMatching ∧ M.IsSpanning

end SubTempGraph

end SimpleTemporalGraph
