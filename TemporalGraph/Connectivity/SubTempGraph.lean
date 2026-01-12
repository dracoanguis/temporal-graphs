import TemporalGraph.Connectivity.Basic
import TemporalGraph.SubTempGraph

universe u
variable {V : Type u} {t : ℕ} {V' : Set V} {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph

namespace SubTempGraph

@[simp]
def Reachable (H : SubTempGraph G) (x y : H.verts) : Prop
:= H.coe.Reachable x y

def IsSpanner (G' : SubTempGraph G) : Prop
:= G'.IsSpanning ∧ ∀ u v : G'.verts, G.Reachable u v → G'.Reachable u v

def IsSpannerOf (H : SubTempGraph G) (H' : SubTempGraph G) : Prop
:= H.verts = H'.verts ∧  ∀ u v , H'.Reachable u v → H.spanningCoe.Reachable u v

def TemporallyConnected (G' : SubTempGraph G) : Prop
:= ∀ u v , G'.coe.Reachable u v

def IsTCSpanner (G' : SubTempGraph G) : Prop :=
  (G'.IsSpanning) ∧ (TemporallyConnected G')

protected lemma temporallyConnected_iff {G' : SubTempGraph G}
: G'.TemporallyConnected ↔ G'.coe.TemporallyConnected
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
lemma subgraph_reachable_is_reachable
{V : Type u} {G : SimpleTemporalGraph V} {G' : SubTempGraph G}
: ∀ u v, G'.coe.Reachable u v → G.Reachable ↑u ↑v
:= by
  intro u v h
  rw [reachable_iff_nonempty_univ] at h
  let ⟨s, ⟨t, ⟨tw, h⟩⟩⟩ := h
  rw [reachable_iff_nonempty_univ]
  exact ⟨s, ⟨t, ⟨tw, h⟩⟩⟩

@[simp]
lemma subgraph_reachable_is_reachable' {H : SubTempGraph G} {H' : SubTempGraph G}
(h : H ≤ H')
: ∀ u v, H.Reachable u v → H'.Reachable ⟨u, Set.mem_of_subset_of_mem h.left u.prop⟩
                                        ⟨v, Set.mem_of_subset_of_mem h.left v.prop⟩
:= by
  intro x y
  sorry

@[simp]
protected lemma TCspanner_imply_TC (G' : SubTempGraph G)
: G'.IsTCSpanner → G.TemporallyConnected
:= by
  intro ⟨h_span,h_tc⟩
  unfold TemporallyConnected at h_tc
  rw [SubTempGraph.IsSpanning] at h_span
  rw [SimpleTemporalGraph.TemporallyConnected]
  simp [h_span] at h_tc
  intro u v
  let u' : Subtype G'.verts := ⟨u, h_span u⟩
  let v' : Subtype G'.verts := ⟨v, h_span v⟩
  let ⟨s, ⟨t, ⟨tw⟩⟩⟩ :=  h_tc u v
  exact ⟨s, ⟨t, ⟨tw.lift_subtempgraph_walk⟩⟩⟩

@[simp]
theorem spanningCoe_eq_coe_reachability (H : SubTempGraph G)
: ∀ x y, H.Reachable x y ↔ H.spanningCoe.Reachable x y
:= by
  intro x y
  simp
  constructor
  · sorry
  · sorry

theorem top_reachability : ∀ x y, (⊤ : SubTempGraph G).Reachable x y ↔ G.Reachable x y
:= by
  intro x y
  constructor
  · exact SubTempGraph.subgraph_reachable_is_reachable x y
  · intro h ; rw [spanningCoe_eq_coe_reachability] ; rw [top_spanningCoe] ; exact h

theorem addVerts_reachability {s : Set V} {H : SubTempGraph G}
: ∀ x y, H.Reachable x y ↔ (H.addVerts s).Reachable ⟨x, by simp⟩ ⟨y, by simp⟩
:= by
  intro x y
  simp
  constructor
  · sorry
  · sorry

theorem addEdge_reachability {u v : V} {H : SubTempGraph G}
{h : G.Adj u v t} {h' : u ∈ H.verts ∧ v ∈ H.verts}
: ∀ x y, H.Reachable x y → (H.addEdge h h').Reachable x y
:= by
  intro x y
  sorry

theorem deleteVerts_reachability {s : Set V} {H : SubTempGraph G}
: ∀ x y, (H.deleteVerts s).Reachable x y ↔ H.Reachable
  ⟨x, by have h := (deleteVerts_le H s).left ; rw [Set.subset_def] at h ; cases x with
  |mk x hx => exact h x hx⟩
  ⟨y, by have h := (deleteVerts_le H s).left ; rw [Set.subset_def] at h ; cases y with
  |mk y hy => exact h y hy⟩
:= by
  intro x y
  simp
  constructor
  · sorry -- exact SubTempGraph.subgraph_reachable_is_reachable x y
  · sorry

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


def spanner_from2 {u v w : V} {t₁ t₂ : ℕ} {G}
(hG : G.EarliestEdge v u t₁ ∧ G.LatestEdge w u t₂)
(R : SubTempGraph G)
: SubTempGraph G where
  verts := Set.univ
  Adj x y t := (x≠u ∧ y≠u ∧ R.Adj x y t)
              ∨ (x=u∧y=v∧t=t₁) ∨ (y=u∧x=v∧t=t₁)
              ∨ (x=u∧y=w∧t=t₂) ∨ (y=u∧x=w∧t=t₂)

  adj_sub := by
    intro x y t hAdj
    let hEE := hG.left
    rw [SimpleTemporalGraph.EarliestEdge] at hEE
    let hEEedge := hEE.left
    let hLE := hG.right
    rw [SimpleTemporalGraph.LatestEdge] at hLE
    let hLEedge := hLE.left
    cases hAdj with
    | inl h => exact R.adj_sub h.right.right
    | inr h => cases h with
      | inl h => rw [h.left.symm, h.right.left.symm, h.right.right.symm] at hEEedge ; exact hEEedge.symm
      | inr h => cases h with
        | inl h => rw [h.left.symm, h.right.left.symm, h.right.right.symm] at hEEedge ; exact hEEedge
        | inr h => cases h with
          | inl h => rw [h.left.symm, h.right.left.symm, h.right.right.symm] at hLEedge ; exact hLEedge.symm
          | inr h => rw [h.left.symm, h.right.left.symm, h.right.right.symm] at hLEedge ; exact hLEedge

  edge_vert := by
    intro x y t h
    trivial

  symm := by
    intro t x y h
    cases h with
    | inl h => exact Or.inl ⟨h.right.left, ⟨h.left, R.symm t h.right.right⟩⟩
    | inr h => cases h with
      | inl h => exact Or.inr (Or.inr (Or.inl h))
      | inr h => cases h with
        | inl h => exact Or.inr (Or.inl h)
        | inr h => cases h with
          | inl h => exact Or.inr (Or.inr (Or.inr (Or.inr h)))
          | inr h => exact Or.inr (Or.inr (Or.inr (Or.inl h)))


lemma spanner_construct2 {u v w : V} {t₁ t₂ : ℕ} {G}
(hG : G.EarliestEdge v u t₁ ∧ G.LatestEdge w u t₂)
(R : SubTempGraph G) (hR : R.IsSpannerOf <| G.toSubgraphTop.deleteVerts {u})
: (R.spanner_from2 hG).IsSpanner
:= by sorry
  -- let S := R.spanner_from2 hG
  -- change S.IsSpanner
  -- have hSee : S.coe.EarliestEdge ⟨v, Set.mem_univ v⟩ ⟨u, Set.mem_univ u⟩ t₁ := by
  --   rw [SimpleTemporalGraph.EarliestEdge]
  --   constructor
  --   · sorry --exact SubTempGraph.Adj.coe
  --   · sorry
  -- have hfur := fun x : S.verts ↦ earliest_edge_reachability hSee x
  -- have htur := sorry --fun x : S.verts ↦ latest_edge_reachability hle x (htc' x ⟨w, hwin⟩)
  -- have huu := earliest_latest_edge_co_reachability hee hle (htc' ⟨v, hvin⟩ ⟨w, hwin⟩)
  -- rw [SubTempGraph.IsSpanner]
  -- apply And.intro
  -- · rw [isSpanning_iff]
  --   rfl
  -- · intro x y h
  --   by_cases hcase : x = u
  --   · by_cases hcase' : y = u
  --     ·

def spannerFrom3 {u v w : V} {t₁ t₂ : ℕ} {G} {R : SubTempGraph G}
(hG : G.EarliestEdge v u t₁ ∧ G.LatestEdge w u t₂)
(hR : R.IsSpannerOf <| (⊤ : SubTempGraph G).deleteVerts {u})
: SubTempGraph G :=
  have hE₁ : G.Adj v u t₁ := hG.left.left
  have hV : ∀ x, x ∈ (R.addVerts {u}).verts := by
    rw [IsSpannerOf] at hR
    let hR := hR.left
    rw [deleteVerts_verts] at hR
    rw [addVerts_verts, hR, top_verts]
    simp
  have hV₁ : v ∈ (R.addVerts {u}).verts ∧ u ∈ (R.addVerts {u}).verts := And.intro (hV v) (hV u)
  have hE₂ : G.Adj w u t₂ := hG.right.left
  have hV₂ : w ∈ (R.addVerts {u}).verts ∧ u ∈ (R.addVerts {u}).verts := And.intro (hV w) (hV u)
((R.addVerts {u}).addEdge hE₁ hV₁).addEdge hE₂ hV₂

lemma spannerConstruct3 {u v w : V} {t₁ t₂ : ℕ} {G} {R : SubTempGraph G}
(hG : G.EarliestEdge v u t₁ ∧ G.LatestEdge w u t₂)
(hR : R.IsSpannerOf <| (⊤ : SubTempGraph G).deleteVerts {u})
: (spannerFrom3 hG hR).IsSpanner
:= by
  rw [spannerFrom3]
  have hSpanning : (R.addVerts {u}).IsSpanning := by
    rw [isSpanning_iff]
    rw [IsSpannerOf] at hR
    let hR := hR.left
    rw [deleteVerts_verts] at hR
    rw [addVerts_verts, hR, top_verts]
    simp
  have hRreach : ∀ (x y : R.verts), G.Reachable x y → R.Reachable x y := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    rw [spanningCoe_eq_coe_reachability]
    let hin := hR.left
    let h' := (hR.right ⟨x, by rwa [hin] at hx⟩ ⟨y, by rwa [hin] at hy⟩)
    conv at h' => lhs ; rw [deleteVerts_reachability, top_reachability]
    exact h' h
  have hrl := hR.left
  have hRSreach : ∀ (x y : R.verts), G.Reachable x y → (spannerFrom3 hG hR).Reachable ⟨x, hSpanning x⟩ ⟨y, hSpanning y⟩ := by
    intro x y hreach
    simp [spannerFrom3]
    have h' := hRreach x y
    rw [addVerts_reachability] at h'
    exact addEdge_reachability _ _
      <| addEdge_reachability _ _
      <| h' hreach
  have hes :
    (spannerFrom3 hG hR).coe.EarliestEdge ⟨v, hSpanning v⟩ ⟨u, hSpanning u⟩ t₁
    ∧ (spannerFrom3 hG hR).coe.LatestEdge ⟨w, hSpanning w⟩ ⟨u, hSpanning u⟩ t₂
    := by
    constructor
    · apply EarliestEdge_graph_isof_subgraph
      · exact hG.left
      · unfold spannerFrom3 ; left ; simp [addEdge_edge]
    · apply LatestEdge_graph_isof_subgraph
      · exact hG.right
      · unfold spannerFrom3 ; right ; simp
  have hfu : ∀ y : R.verts , G.Reachable u y → (spannerFrom3 hG hR).Reachable ⟨u, hSpanning u⟩ ⟨y, hSpanning y⟩ := by
    sorry
    -- intro y hreach
    -- rw [reachable_iff_nonempty_TemporalWalkset] at hreach
    -- exact hRSreach ⟨u, hSpanning u⟩ ⟨y, hSpanning y⟩ hreach
  have htu : ∀ x : R.verts, G.Reachable x u → (spannerFrom3 hG hR).Reachable ⟨x, hSpanning x⟩ ⟨u, hSpanning u⟩ := by sorry
  have huu : G.Reachable u u → (spannerFrom3 hG hR).Reachable ⟨u, hSpanning u⟩ ⟨u, hSpanning u⟩ := by sorry
  constructor
  · exact hSpanning
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hreach
    push_cast at hreach
    by_cases hcase : x=u
    conv => lhs ; lhs ; rw [hcase]
    · by_cases hcase' : y=u
      · conv => rhs ; lhs ; rw [hcase']
        rw [hcase, hcase'] at hreach
        exact huu hreach
      · rw [hcase] at hreach
        exact hfu ⟨y, by rw [hrl] ; simp ; rw [top_verts] ; exact ⟨trivial, hcase'⟩⟩ hreach
    · by_cases hcase' : y=u
      · conv => rhs ; lhs ; rw [hcase']
        rw [hcase'] at hreach
        exact htu ⟨x, by rw [hrl] ; simp ; rw [top_verts] ; exact ⟨trivial, hcase⟩⟩ hreach
      · let x' : R.verts := ⟨x, by rw [hrl] ; simp ; rw [top_verts] ; exact ⟨trivial, hcase⟩⟩
        let y' : R.verts := ⟨y, by rw [hrl] ; simp ; rw [top_verts] ; exact ⟨trivial, hcase'⟩⟩
        exact hRSreach x' y' hreach



end SubTempGraph
end SimpleTemporalGraph
