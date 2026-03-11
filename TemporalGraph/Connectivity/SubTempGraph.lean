import TemporalGraph.Connectivity.Basic
import TemporalGraph.SubTempGraph

universe u
variable {V : Type u} {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph

namespace SubTempGraph

@[simp]
def Reachable (H : SubTempGraph G) (x y : H.Verts) : Prop
:= H.coe.Reachable x y

def IsSpanner (H : SubTempGraph G) : Prop
:= H.IsSpanning ∧ ∀ x y : H.Verts, G.Reachable x y → H.Reachable x y

def IsSpannerOf (H : SubTempGraph G) (H' : SubTempGraph G) : Prop
:= H.Verts = H'.Verts ∧  ∀ u v , H'.Reachable u v → H.spanningCoe.Reachable u v

def TemporallyConnected (H : SubTempGraph G) : Prop
:= ∀ x y : H.Verts , H.Reachable x y

def IsTCSpanner (H : SubTempGraph G) : Prop :=
  (H.IsSpanning) ∧ (H.TemporallyConnected)

protected lemma temporallyConnected_iff {H : SubTempGraph G}
: H.TemporallyConnected ↔ H.coe.TemporallyConnected
:= by
  apply Iff.intro
  · unfold TemporallyConnected
    intro h
    unfold SimpleTemporalGraph.TemporallyConnected
    trivial
  · unfold TemporallyConnected
    intro h
    rw [SimpleTemporalGraph.TemporallyConnected] at h
    trivial

@[simp]
lemma reachable_of_subTempGraph_reachable {H : SubTempGraph G}
: ∀ x y : H.Verts, H.Reachable x y → G.Reachable ↑x ↑y
:= by
  intro _ _ h
  rw [Reachable, reachable_iff_nonempty_univ] at h
  have ⟨n, ⟨m, ⟨p, h⟩⟩⟩ := h
  rw [reachable_iff_nonempty_univ]
  exact ⟨n, ⟨m, ⟨p, h⟩⟩⟩

@[simp]
lemma reachable_of_subTempGraph_reachable' {H : SubTempGraph G} {H' : SubTempGraph G}
(h : H ≤ H')
: ∀ x y : H.Verts, H.Reachable x y → H'.Reachable
  ⟨x, Set.mem_of_subset_of_mem h.left x.prop⟩
  ⟨y, Set.mem_of_subset_of_mem h.left y.prop⟩
:= by
  intro _ _ ⟨n, m, ⟨p⟩⟩
  exact ⟨n, m, ⟨p.lift_subtempgraph_walk' h⟩⟩


@[simp]
protected lemma temporallyConnected_of_TCSpanner (H : SubTempGraph G)
: H.IsTCSpanner → G.TemporallyConnected
:= by
  intro ⟨h_span, h_tc⟩
  unfold TemporallyConnected at h_tc
  rw [SubTempGraph.IsSpanning] at h_span
  rw [SimpleTemporalGraph.TemporallyConnected]
  simp only [Reachable, Subtype.forall, h_span, forall_true_left] at h_tc
  intro x y
  let ⟨n, ⟨m, ⟨p⟩⟩⟩ :=  h_tc x y
  exact ⟨n, ⟨m, ⟨p.lift_subtempgraph_walk⟩⟩⟩

-- theorem reachability_imp_spanningCoe_reachability (H : SubTempGraph G)
-- : ∀ x y, H.Reachable x y → H.spanningCoe.Reachable x y
-- := by
--   intro ⟨x, hx⟩ ⟨y, hy⟩
--   sorry

-- theorem top_reachability : ∀ x y, (⊤ : SubTempGraph G).Reachable x y ↔ G.Reachable x y
-- := by
--   intro x y
--   constructor
--   · exact SubTempGraph.subgraph_reachable_is_reachable _ _
--   · sorry

theorem addVerts_reachability {s : Set V} {H : SubTempGraph G}
: ∀ x y : H.Verts, H.Reachable x y → (H.addVerts s).Reachable ⟨x, by simp⟩ ⟨y, by simp⟩
:= by exact reachable_of_subTempGraph_reachable' addVerts_le

theorem addEdge_reachability {x y : V} {n : ℕ} {H : SubTempGraph G} {h : G.Adj x y n}
{h₁ : x ∈ H.Verts ∧ y ∈ H.Verts}
: ∀ x y : H.Verts, H.Reachable x y → (H.addEdge h h₁).Reachable x y
:= by exact reachable_of_subTempGraph_reachable' addEdge_le

theorem deleteVerts_reachability {s : Set V} {H : SubTempGraph G}
: ∀ x y : (H.deleteVerts s).Verts, (H.deleteVerts s).Reachable x y → H.Reachable
  ⟨x, by have h := (deleteVerts_le' H s).left ; rw [Set.subset_def] at h ; cases x with
  |mk x hx => exact h x hx⟩
  ⟨y, by have h := (deleteVerts_le' H s).left ; rw [Set.subset_def] at h ; cases y with
  |mk y hy => exact h y hy⟩
:= by exact reachable_of_subTempGraph_reachable' deleteVerts_le

-- /-- A temporal graphe admits a spanner if and only if it is Temporally Connected -/
-- @[simp]
-- theorem TCspanner_iff_TC (G : SimpleTemporalGraph V)
-- : (∃ (G' : SubTempGraph G), G'.IsTCSpanner) ↔ G.TemporallyConnected
-- := by
--   unfold SubTempGraph.IsTCSpanner
--   apply Iff.intro
--   · intro ⟨G', ⟨h_span,h_tc⟩⟩
--     unfold TemporallyConnected at h_tc
--     rw [SubTempGraph.IsSpanning] at h_span
--     rw [TemporallyConnected]
--     simp [h_span] at h_tc
--     intro u v
--     let u' : Subtype G'.verts := ⟨u, h_span u⟩
--     let v' : Subtype G'.verts := ⟨v, h_span v⟩
--     let ⟨t, ⟨tw⟩⟩ :=  h_tc u v
--     exact ⟨t, ⟨tw.lift_subtempgraph_walk⟩⟩

--   · intro h_tc
--     let G' : SubTempGraph G := {
--       verts := Set.univ
--       Adj := G.Adj
--       adj_sub := by
--         intro u v t h
--         trivial
--       symm := G.symm
--       edge_vert := by
--         intro v w t h
--         trivial
--     }
--     have h_span : G'.IsSpanning := by
--       rw [SubTempGraph.isSpanning_iff]
--     have h'_tc : G'.coe.TemporallyConnected := by
--       rw [TemporallyConnected]
--       intro u v
--       unfold TemporallyConnected Reachable at h_tc
--       rw [Reachable]

--     exact ⟨G', ⟨h_span, h_tc⟩⟩

-- def spannerFrom3 {u v w : V} {t₁ t₂ : ℕ} {G} {R : SubTempGraph G}
-- (hG : G.EarliestEdge v u t₁ ∧ G.LatestEdge w u t₂)
-- (hR : R.IsSpannerOf <| (⊤ : SubTempGraph G).deleteVerts {u})
-- : SubTempGraph G :=
--   have hE₁ : G.Adj v u t₁ := hG.left.left
--   have hV : ∀ x, x ∈ (R.addVerts {u}).verts := by
--     rw [IsSpannerOf] at hR
--     let hR := hR.left
--     rw [deleteVerts_verts] at hR
--     rw [addVerts_verts, hR, top_verts]
--     simp
--   have hV₁ : v ∈ (R.addVerts {u}).verts ∧ u ∈ (R.addVerts {u}).verts := And.intro (hV v) (hV u)
--   have hE₂ : G.Adj w u t₂ := hG.right.left
--   have hV₂ : w ∈ (R.addVerts {u}).verts ∧ u ∈ (R.addVerts {u}).verts := And.intro (hV w) (hV u)
-- ((R.addVerts {u}).addEdge hE₁ hV₁).addEdge hE₂ hV₂

end SubTempGraph
end SimpleTemporalGraph
