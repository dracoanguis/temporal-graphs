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

@[simp]
protected theorem irrefl {G : SimpleTemporalGraph V} {v : V} {t : ℕ} : ¬G.Adj v v t :=
  G.loopless t v

section Adjacency

variable {G : SimpleTemporalGraph V} {u v : V} {t : ℕ}

theorem adj_comm (u v : V) (t : ℕ) : G.Adj u v t ↔ G.Adj v u t :=
  ⟨fun x => G.symm t x, fun x => G.symm t x⟩

@[symm]
theorem adj_symm (h : G.Adj u v t) : G.Adj v u t :=
  G.symm t h

theorem Adj.symm (h : G.Adj u v t) : G.Adj v u t :=
  G.symm t h

theorem ne_of_adj {a b : V} {t : ℕ} (h : G.Adj a b t) : a ≠ b := by
  rintro rfl
  exact G.irrefl h

protected theorem Adj.ne {a b : V} {t : ℕ} (h : G.Adj a b t) : a ≠ b :=
  G.ne_of_adj h

protected theorem Adj.ne' {a b : V} {t : ℕ} (h : G.Adj a b t) : b ≠ a :=
  h.ne.symm

end Adjacency

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

-- @[simp]
-- theorem isSubtempgraph_self (G : SimpleTemporalGraph V) : G.IsSubtempgraph G := by
--   unfold IsSubtempgraph
--   intro _ _ _ h
--   exact h

-- def support :=
  -- SetRel.dom {(u, v, t) : V ⨯ V ⨯ ℕ | G.Adj u v t}



-- instance neighborSet.memDecidable (G : SimpleTemporalGraph V) (v : V) [DecidableRel (λ x y↦ ∃ t, G.Adj x y t)] :
--     DecidablePred (· ∈ G.neighborSet v) :=
--   inferInstanceAs <| DecidablePred (Adj G v)

def IsComplete (G : SimpleTemporalGraph V) : Prop :=
  ∀ u v : V, ∃ t, G.Adj u v t

-- check alt way fo writing
def IsProper (G : SimpleTemporalGraph V) : Prop :=
  --∀ u : V, ¬∃ t : ℕ, ∃ v w : V, G.Adj u v t ∧ G.Adj u w t
  ∀ u v w, ∀ t, G.Adj u v t ∧ G.Adj u w t → v = w

/- The *earliest edge* of *α*, with *β* destination at *t*-/
def EarliestEdge (G : SimpleTemporalGraph V) (α β : V) (t : ℕ) : Prop :=
  G.Adj α β t ∧ ∀ w t', G.Adj α w t' → t ≤ t'

/- The *latest edge* of *α*, with *β* destination at *t*-/
def LatestEdge (G : SimpleTemporalGraph V) (α β : V) (t : ℕ) : Prop :=
  G.Adj α β t ∧ ∀ w t', G.Adj α w t' → t ≥ t'


section Order

def IsSubtempgraph {V' : Set V} (G : SimpleTemporalGraph V) (G' : SimpleTemporalGraph V') : Prop :=
  ∀ {v w : V'} {t : ℕ}, G'.Adj v w t → G.Adj ↑v ↑w t

/- This is a Subgraph with the same vertex set-/
def IsSubtempgraphOnV (x y : SimpleTemporalGraph V) : Prop :=
  ∀ {v w : V} {t : ℕ}, x.Adj v w t → y.Adj v w t

instance : LE (SimpleTemporalGraph V) :=
  ⟨IsSubtempgraphOnV⟩

lemma le_iff_adj {G H : SimpleTemporalGraph V} :
G ≤ H ↔ ∀ v w t, G.Adj v w t → H.Adj v w t := .rfl

@[simp]
theorem isSubtempgraphOnV_eq_le
: (IsSubtempgraphOnV : SimpleTemporalGraph V -> SimpleTemporalGraph V -> Prop) = (· ≤ ·)
:= rfl

instance : Bot (SimpleTemporalGraph V) where
  bot := {
    Adj _ _ _ := False
    symm := by
      intro _ _ _ h
      trivial
    loopless := by
      intro _ _ h
      trivial
  }

end Order

end SimpleTemporalGraph
