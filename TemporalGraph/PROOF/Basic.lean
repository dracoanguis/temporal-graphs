import TemporalGraph.Basic
import TemporalGraph.SubTempGraph

universe u

variable {V : Type u}

namespace SimpleTemporalGraph

def EarliestNeigbhor {G : SimpleTemporalGraph V} (α u : V) : Prop := ∃ t, G.EarliestEdge α u t
def LatestNeighbor {G : SimpleTemporalGraph V} (β u : V) : Prop := ∃ t, G.LatestEdge β u t


namespace SubTempGraph

variable {G : SimpleTemporalGraph V}

def EarliestEdge (G' : SubTempGraph G) (α u : V) (t : ℕ) : Prop
:= G'.Adj α u t ∧ ∀ w t', G'.Adj α w t' → t ≤ t'

def LatestEdge (G' : SubTempGraph G) (β u : V) (t : ℕ) : Prop
:= G'.Adj β u t ∧ ∀ w t', G'.Adj β w t' → t' ≤ t

def EarliestNeigbhor {G' : SubTempGraph G} (α u : V) : Prop := ∃ t, G'.EarliestEdge α u t

def LatestNeighbor {G' : SubTempGraph G} (β u : V) : Prop := ∃ t, G'.LatestEdge β u t

theorem EarliestEdge_exists {G' : SubTempGraph G} (u : V) (h : ∃ v t, G'.Adj u v t)
: ∃ w t', G'.EarliestEdge u w t'
:= by
  sorry

def IsClique (G' : SubTempGraph G) : Prop
:= ∀ (u v : G'.verts), u ≠ v → ∃ t, G'.Adj u v t

def IsProper (G' : SubTempGraph G) : Prop
:= ∀ u v w t, G'.Adj u v t ∧ G'.Adj u w t → v=w

-- From SimpleGraph.Subgraph.IsMatching
def IsMatching (M : SubTempGraph G) : Prop
:= ∀ ⦃v : V⦄, v ∈ M.verts → ∃! w , ∃ t, M.Adj v w t

-- From SimpleGraph.Subgraph.IsPerfectMatching
def IsPerfectMatching (M : SubTempGraph G)
:= M.IsMatching ∧ M.IsSpanning

end SubTempGraph

end SimpleTemporalGraph
