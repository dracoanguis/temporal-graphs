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

-- -- Given `h : H.Adj u v`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩`.
-- protected theorem Adj.coe {H : G.SubTempGraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    -- H.coe.Adj ⟨u, H.edge_vert h⟩ ⟨v, H.edge_vert (h.symm t)⟩ := h

-- instance (G : SimpleGraph V) (H : SubTemporalGraph G) [DecidableRel H.Adj]
--: DecidableRel H.coe.Adj
--:= fun a b ↦ ‹DecidableRel H.Adj› _ _

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

@[simps]
def induce (G' : G.SubTempGraph) (s : Set V) : G.SubTempGraph where
  verts := s
  Adj u v t := u ∈ s ∧ v ∈ s ∧ G'.Adj u v t
  adj_sub h := G'.adj_sub h.2.2
  edge_vert h := h.1
  symm t _ _ h := ⟨h.2.1, h.1, G'.symm t h.2.2⟩

-- theorem _root_.SimpleTemporalGraph.induce_eq_coe_induce_top (s : Set V) :
--     G.induce s = ((⊤ : G.SubTempGraph).induce s).coe := by
--   ext
--   simp


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

end SimpleTemporalGraph
