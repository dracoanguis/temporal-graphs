import TemporalGraph.Init
import Mathlib


macro (name := aesop_temporal_graph) "aesop_temporal_graph" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `SimpleTemporalGraph):ident]))



universe u

/-- The simplest undirected temporal graph with edges only present at one time
(not proper by definition) -/
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

def IsSubtempgraph (x y : SimpleTemporalGraph V) : Prop :=
  ∀ {v w : V} {t : ℕ}, x.Adj v w t → y.Adj v w t

instance : LE (SimpleTemporalGraph V) :=
  ⟨IsSubtempgraph⟩

@[simp]
theorem isSubtempgraph_eq_le :
  (IsSubtempgraph : SimpleTemporalGraph V -> SimpleTemporalGraph V -> Prop) = (· ≤ ·) :=
  rfl

@[simp]
theorem isSubtempgraph_self (G : SimpleTemporalGraph V) : G.IsSubtempgraph G := by
  unfold IsSubtempgraph
  intro _ _ _ h
  exact h

-- def support :=
  -- SetRel.dom {(u, v, t) : V ⨯ V ⨯ ℕ | G.Adj u v t}

end SimpleTemporalGraph
