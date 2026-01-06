import TemporalGraph.Basic
import TemporalGraph.TemporalWalk

universe u

namespace SimpleTemporalGraph


@[ext]
structure SubTempGraph {V : Type u} (G : SimpleTemporalGraph V) where
  verts : Set V
  Adj : V → V → ℕ → Prop

  adj_sub : ∀ {u v : V} {t : ℕ}, Adj u v t → G.Adj u v t
  edge_vert : ∀ {v w : V} {t : ℕ}, Adj v w t → v ∈ verts
  symm : ∀ t, Symmetric (fun v w => Adj v w t)

namespace SubTempGraph

variable {V : Type u} {G : SimpleTemporalGraph V}

protected def mk' {V' : Set V} (G' : SimpleTemporalGraph V') (h : G.IsSubtempgraph G')
: SubTempGraph G
:= {
  verts := V'
  Adj := fun v w t =>
    ∃ hv : v ∈ V', ∃ hw : w ∈ V', G'.Adj ⟨v, hv⟩ ⟨w, hw⟩ t,

  adj_sub := by
    intro u v t h'
    rcases h' with ⟨hv, hw, h'⟩
    exact h h'

  edge_vert := by
    intro u v t h'
    rcases h' with ⟨hv, _, _⟩
    exact hv

  symm := by
    intro t u v  h'
    rcases h' with ⟨hv, hw, h'⟩
    exact ⟨hw, hv, G'.symm t h' ⟩
}

protected theorem loopless (G' : SubTempGraph G) : ∀ t, Irreflexive (fun v w ↦ G'.Adj v w t) :=
  fun t v h ↦ G.loopless t v (G'.adj_sub h)

theorem adj_comm (G' : SubTempGraph G) (v w : V) (t : ℕ) : G'.Adj v w t ↔ G'.Adj w v t :=
  ⟨fun x ↦ G'.symm t x, fun x ↦ G'.symm t x⟩

@[symm]
theorem adj_symm (G' : SubTempGraph G) {u v : V} {t : ℕ} (h : G'.Adj u v t) : G'.Adj v u t :=
  G'.symm t h

protected theorem Adj.symm {G' : SubTempGraph G} {u v : V} {t : ℕ} (h : G'.Adj u v t)
: G'.Adj v u t
:= G'.symm t h

protected theorem Adj.adj_sub {H : G.SubTempGraph} {u v : V} {t : ℕ} (h : H.Adj u v t)
: G.Adj u v t
:= H.adj_sub h

protected theorem Adj.fst_mem {H : G.SubTempGraph} {u v : V} {t : ℕ} (h : H.Adj u v t)
: u ∈ H.verts
:= H.edge_vert h

protected theorem Adj.snd_mem {H : G.SubTempGraph} {u v : V} {t : ℕ} (h : H.Adj u v t)
: v ∈ H.verts
:= h.symm.fst_mem

-- protected theorem Adj.ne {H : G.SubTemporalGraph} {u v : V} {t : ℕ} (h : H.Adj u v t)
-- : u ≠ v
-- := h.adj_sub.ne

/-- Coercion from `G' : SubTemporalGraph G` to a `SimpleTemporalGraph G'.verts`. -/
@[simps, coe]
protected def coe (G' : SubTempGraph G) : SimpleTemporalGraph G'.verts where
  Adj v w t := G'.Adj v w t
  symm t _ _ h := G'.symm t h
  loopless t v h := loopless G t v (G'.adj_sub h)

-- Seems a bit weird for it to work should check on site
instance {V : Type u} {G : SimpleTemporalGraph V} {G' : SubTempGraph G}
: Coe (SubTempGraph G) (SimpleTemporalGraph G'.verts) where
  coe H := {
    Adj v w t := H.Adj v w t
    symm t _ _ h := H.symm t h
    loopless t v h := loopless G t v (H.adj_sub h)
  }

@[simp]
theorem Adj.adj_sub' (G' : SubTempGraph G) (u v : G'.verts) (t : ℕ) (h : G'.Adj u v t)
: G.Adj u v t
:= G'.adj_sub h

theorem coe_adj_sub (G' : SubTempGraph G) (u v : G'.verts) (t : ℕ) (h : G'.coe.Adj u v t)
: G.Adj u v t
:= G'.adj_sub h

-- Given `h : H.Adj u v t`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩ t`.
protected theorem Adj.coe {H : G.SubTempGraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    H.coe.Adj ⟨u, h.fst_mem⟩ ⟨v, h.snd_mem⟩ t := h

-- instance (G : SimpleGraph V) (H : SubTempGraph G) [DecidableRel H.Adj]
-- : DecidableRel H.coe.Adj
-- := fun a b ↦ ‹DecidableRel H.Adj› _ _

theorem coe_sub (G' : SubTempGraph G) : G.IsSubtempgraph G'.coe:= by
  rw [SimpleTemporalGraph.IsSubtempgraph]
  intro v w t
  exact coe_adj_sub G' v w t

section Spanning

/-- A SubTempGraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (G' : SubTempGraph G) : Prop :=
  ∀ v : V, v ∈ G'.verts

theorem isSpanning_iff {G' : SubTempGraph G} : G'.IsSpanning ↔ G'.verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

/-- Coercion from `SubTempGraph G` to `SimpleTemporalGraph V`.  If `G'` is a spanning
subgraph, then `G'.spanningCoe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
protected def spanningCoe (G' : SubTempGraph G) : SimpleTemporalGraph V where
  Adj := G'.Adj
  symm := G'.symm
  loopless := G'.loopless

theorem Adj.of_spanningCoe {G' : SubTempGraph G} {u v : G'.verts} {t : ℕ}
(h : G'.spanningCoe.Adj u v t) : G.Adj u v t
:= G'.adj_sub h

lemma spanningcoe_le (G' : SubTempGraph G) : G'.spanningCoe ≤ G := G'.adj_sub

variable {G₁ : SubTempGraph G} {G₂ : SubTempGraph G}

theorem spanningCoe_inj : G₁.spanningCoe = G₂.spanningCoe ↔ G₁.Adj = G₂.Adj := by
  simp [SubTempGraph.spanningCoe]

end Spanning

section Order

instance : Top G.SubTempGraph where
  top := {
    verts := Set.univ
    Adj := G.Adj
    adj_sub := id
    symm := G.symm
    edge_vert := @fun v _ _ _ ↦ Set.mem_univ v
  }

@[simp]
theorem top_adj {x y : V} {t : ℕ} : (⊤ : SubTempGraph G).Adj x y t ↔ G.Adj x y t :=
  Iff.rfl

theorem top_verts : (⊤ : SubTempGraph G).verts = Set.univ := rfl

instance : Bot G.SubTempGraph where
  bot := {
    verts := ∅
    Adj := ⊥
    adj_sub := False.elim
    edge_vert := False.elim
    symm _ _ _ := id
  }

def IsSubgraphOf (H : SubTempGraph G) (H' : SubTempGraph G) : Prop
:= (H.verts ⊆ H'.verts) ∧
    (∀ {u v t}, H.Adj u v t → H'.Adj u v t)

instance : LE (SubTempGraph G) :=
  ⟨IsSubgraphOf⟩

instance : BoundedOrder (SubTempGraph G) where
  top := ⊤
  bot := ⊥
  le_top x := ⟨Set.subset_univ _, by intro _ _ _ h ; rw [top_adj] ; exact x.adj_sub h⟩
  bot_le _ := ⟨Set.empty_subset _, False.elim⟩

end Order

section Induce

/-- A SubTempGraph is called an *induced SubTempGraph* if vertices of `G'` are adjacent if
they are adjacent in `G`. -/
def IsInduced (G' : SubTempGraph G) : Prop :=
  ∀ ⦃v⦄, v ∈ G'.verts → ∀ ⦃w⦄, w ∈ G'.verts → ∀ t, G.Adj v w t → G'.Adj v w t

@[simp] lemma IsInduced.top : (⊤ : G.SubTempGraph).IsInduced := fun _ _ _ _ _ ↦ id

@[simps]
def induce (G' : G.SubTempGraph) (s : Set V) : G.SubTempGraph where
  verts := s
  Adj u v t := u ∈ s ∧ v ∈ s ∧ G'.Adj u v t
  adj_sub h := G'.adj_sub h.2.2
  edge_vert h := h.1
  symm t _ _ h := ⟨h.2.1, h.1, G'.symm t h.2.2⟩



end Induce

end SubTempGraph

namespace TemporalWalk

variable {V : Type u} --{G : SimpleTemporalGraph V} {G' : SubTempGraph G}

@[coe]
protected def lift_subtempgraph_walk {G : SimpleTemporalGraph V} {G' : SubTempGraph G}
{u v : G'.verts} {s t : ℕ} :
G'.coe.TemporalWalk u s v t → G.TemporalWalk ↑u s ↑v t
| single h => single (G'.adj_sub h)
| step h p h' =>
  step (G'.adj_sub h)
    (p.lift_subtempgraph_walk)
    h'

instance {V : Type u} {G : SimpleTemporalGraph V} {G' : SubTempGraph G} {u v : G'.verts} {s t : ℕ} :
Coe (G'.coe.TemporalWalk u s v t) (G.TemporalWalk ↑u s ↑v t) where
  coe := TemporalWalk.lift_subtempgraph_walk

end TemporalWalk


section SubgraphProps

variable {V : Type u} {G : SimpleTemporalGraph V}

@[simps]
def toSubgraph (H : SimpleTemporalGraph V) (h : H ≤ G) : G.SubTempGraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  symm _ := H.symm _

theorem toSubgraph.isSpanning (H : SimpleTemporalGraph V) (h : H ≤ G)
: (toSubgraph H h).IsSpanning
:= Set.mem_univ

def toSubgraphTop : G.SubTempGraph := ⊤

end SubgraphProps

end SimpleTemporalGraph
