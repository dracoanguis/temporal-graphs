import TemporalGraph.Init
import Mathlib


macro (name := aesop_temporal_graph) "aesop_temporal_graph" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `SimpleTemporalGraph):ident]))



universe u

/-- The simplest undirected temporal graph with edges only present at one time -/
@[ext, aesop safe constructors (rule_sets := [SimpleTemporalGraph])]
structure SimpleTemporalGraph (V : Type u) where
  /-- The adjacency labeled by a natural qualifying the time of existance -/
  Adj : V → V → ℕ → Prop
  symm : ∀ t, Symmetric (fun v w => Adj v w t)
  loopless : ∀ t, Irreflexive (fun v w => Adj v w t)



namespace SimpleTemporalGraph

variable {V : Type u}

/-- The Footprint of a SimpleTemporalGraph is a SimpleGraph representing
the edges unlabeled by time. -/
def Footprint (G : SimpleTemporalGraph V) : SimpleGraph V:=
  {
    Adj := fun u v => ∃ t, G.Adj u v t
    symm := by
      intro v w ⟨t, h⟩
      exact ⟨t, G.symm t h⟩
    loopless := by
      intro v ⟨t, h⟩
      exact G.loopless t v h

  }

end SimpleTemporalGraph
