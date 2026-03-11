-- import TemporalGraph.TemporalWalk
-- import TemporalGraph.SubTempGraph
-- import TemporalGraph.Connectivity.SubTempGraph
-- import TemporalGraph.Maps

-- open SimpleTemporalGraph

-- def triangle : SimpleTemporalGraph (Fin 3) :=
--   { Adj := fun v w t =>
--     match t with
--     | 0 => (v=0 ∧ w=1) ∨ (w=0 ∧ v=1)
--     | 1 => (v=1 ∧ w=2) ∨ (w=1 ∧ v=2)
--     | 2 => (v=2 ∧ w=0) ∨ (w=2 ∧ v=0)
--     | _ => False
--     symm := by aesop_temporal_graph
--     loopless := by aesop_temporal_graph
--   }

-- def triangle.path : triangle.TemporalWalk 0 0 1 0 :=
--   TemporalWalk.single (by simp [triangle])

-- def triangle.path' : triangle.TemporalWalk 0 0 2 1 :=
--   TemporalWalk.step (by simp [triangle])
--     <| triangle.path

-- def triangle.path'' : triangle.TemporalWalk 0 0 0 2 :=
--   TemporalWalk.step (by simp [triangle])
--     <| triangle.path'

-- def triangle.path2 : triangle.TemporalWalk 0 0 2 1 :=
--   let e : triangle.Adj 0 1 0 := by simp [triangle]
--   TemporalWalk.single (e)
--     |> TemporalWalk.step (by simp [triangle])

-- #eval triangle.path''.darts

-- #check triangle.Footprint

-- example : triangle.IsProper
-- := by
--   unfold SimpleTemporalGraph.IsProper
--   intro u
--   admit -- way too long and useless

-- #check (triangle.induce ({u : Fin 3 | u ≠ 3})).Adj

import TemporalGraph.SubTempGraph
import TemporalGraph.PROOF.Dismountability

open SimpleTemporalGraph
--open SubTempGraph

universe u
variable {V : Type u} {G : SimpleTemporalGraph V}

-- example {G' : SubTempGraph G} (u : G'.Vplus) (h' : ¬G'.Dismountable2) (h'' : G'.IsClique)
-- (h''' : ∃ w, EarliestNeighborhor u w)
-- : ¬G'.IsClique
-- := by
  -- have ⟨w, hee⟩ := h'''
  -- have h := notDismountable2_neDiff_imp_neigbhorDiff u u h' h'' w w ⟨hee, hee⟩
  -- contradiction

def Square : SimpleTemporalGraph (Fin 4) := {
  Adj := fun v w t =>
    match t with
    | 1 => (v=0 ∧ w=1) ∨ (w=0 ∧ v=1)
    | 2 => (v=1 ∧ w=3) ∨ (w=1 ∧ v=3) ∨ (v=0 ∧ w=2) ∨ (w=0 ∧ v=2)
    | 3 => (v=0 ∧ w=3) ∨ (w=0 ∧ v=3) ∨ (v=1 ∧ w=2) ∨ (w=1 ∧ v=2)
    | 4 => (v=2 ∧ w=3) ∨ (w=2 ∧ v=3)
    | _ => False
  symm := by aesop_temporal_graph
  loopless t := by
    match t with
    -- | 1 => simp only [Fin.isValue] ; constructor ; simp
    -- | 2 => simp only [Fin.isValue] ; constructor ; aesop
    -- | 3 => simp only [Fin.isValue] ; constructor ; aesop
    -- | 4 => simp only [Fin.isValue] ; constructor ; simp
    | _ => split <;> constructor <;> aesop
}

open SubTempGraph

def SubSquare := Square.toSubgraphTop

lemma square_clique : SubSquare.IsClique
:= by
  simp [IsClique, SubSquare, toSubgraphTop, top_verts]
  intro u v _
  match u, v with
  | 0, 1 => simp [Square] ; use 1
  | 1, 0 => simp [Square] ; use 1
  | 0, 2 => use 2 ; simp [Square]
  | 2, 0 => use 2 ; simp [Square]
  | 0, 3 => use 3 ; simp [Square]
  | 1, 2 => use 3 ; simp [Square]
  | 2, 1 => use 3 ; simp [Square]
  | 1, 3 => use 2 ; simp [Square]
  | 2, 3 => use 4 ; simp [Square]
  | 3, 0 => simp [Square] ; use 3
  | 3, 1 => simp [Square] ; use 2
  | 3, 2 => simp [Square] ; use 4
  | 3, 3 => aesop_temporal_graph

-- lemma square_not_dis2 : ¬SubSquare.Dismountable2
-- := by
--   unfold Dismountable2
--   simp only [square_clique, exists_and_left, true_and, not_exists, not_and, not_or, not_le]
--   intro u hee
--   unfold SubTempGraph.LatestNeighbor SubTempGraph.LatestEdge
--   simp? [SubSquare, toSubgraphTop, top_adj]
--   constructor
--   · intro v t hadj
--     match u, v, t with
--     | 0, 1, 1 => simp [Square] ; use 2, 3 ; simp
--     | 0, 2, 2 => simp [Square] ; use 3, 4 ; simp
--     | 0, 3, 3 => simp [Square] ; use 2, 4 ; simp
--     | 1, 0, 1 => simp [Square] ; use 2, 2 ; simp
--     | 1, 2, 3 => simp [Square] ; use 3, 4 ; simp
--     | 1, 3, 2 => simp [Square] ; use 2, 4 ; simp
--     | 2, 0, 2 => simp [Square] ; use 3, 3 ; simp
--     | 2, 1, 3 => simp [Square] ; use 0, 1 ;
--     | 2, 3, 4 => simp [Square] ; use 2, 4 ; sorry
--     | 3, 0, 3 => simp [Square] ; use 3, 3 ; sorry
--     | 3, 1, 2 => simp [Square] ; use 2, 3 ; simp
--     | 3, 2, 4 => simp [Square] ; sorry


-- lemma square_not_dis2' : ¬SubSquare.Dismountable2
-- := by
--   by_contra ⟨hClique, u, hDis⟩
--   unfold SubTempGraph.LatestNeighbor SubTempGraph.LatestEdge SubTempGraph.EarliestNeigbhor SubTempGraph.EarliestEdge at hDis
--   match u with
--   | 0 => obtain ⟨hee, hle⟩ := hDis ;
--           simp at hee hle ;
--           apply hle.elim ;
--           · intro ⟨β, t, hle, hle'⟩ ;
--             match β with
--             | 1 =>


-- lemma square_not_dis2'' : ¬SubSquare.Dismountable2
-- := by
--   unfold Dismountable2
--   simp only [square_clique, exists_and_left, true_and, not_exists, not_and_or, not_or, not_le]
--   intro u
--   unfold SubTempGraph.LatestNeighbor SubTempGraph.LatestEdge SubTempGraph.EarliestNeigbhor SubTempGraph.EarliestEdge
--   conv => lhs ; simp only [SubSquare, toSubgraphTop, top_adj, not_exists, not_and, not_forall, Classical.not_imp,
--     not_le]
--   conv => rhs ; lhs ; simp only [SubSquare, toSubgraphTop, top_adj, not_exists, not_and, not_forall, Classical.not_imp,
--     not_le]
--   conv => rhs ; rhs ; simp only [SubSquare, toSubgraphTop, top_adj, not_exists, not_and_or, not_forall, not_le, exists_prop, Fin.isValue]
--   match u with
--   | 0 => right ; constructor ; intro v t hadj ;
--             (match v with
--               | 1 => by_cases h : t=1 ; use 2, 3 ; simp [Square, h] ; absurd h ; simp [Square] at hadj ; aesop
--               | 2 => by_cases h : t=2 ; use 3, 4 ; simp [Square, h] ; absurd h ; simp [Square] at hadj ; aesop
--               | 3 => by_cases h : t=3 ; use 2, 4 ; simp [Square, h] ; absurd h ; simp [Square] at hadj ; aesop
--               | 0 => grind [Square] ) ;
--             ( intro v w t ;
--               match v with
--               | 1 => (match )
--             )
--   | _ => sorry


-- lemma square_not_dis2''' : ¬SubSquare.Dismountable2 := by
--   unfold Dismountable2
--   simp only [square_clique, exists_and_left, true_and, not_exists, not_and_or, not_or, not_le]
--   unfold SubSquare SubTempGraph.LatestNeighbor SubTempGraph.LatestEdge
--     SubTempGraph.EarliestNeigbhor SubTempGraph.EarliestEdge
--   push_neg
--   simp only [toSubgraphTop, top_adj]
--   intro u
--   fin_cases u
--   · right
--     constructor
--     · intro v t hadj
--       fin_cases v <;> simp_all [Square]
--       · by_cases h : t=1 ; use 2, 3 ; simp [h] ; absurd h ; aesop
--       · by_cases h : t=2 ; use 3, 4 ; simp [h] ; absurd h ; aesop
--       · by_cases h : t=3 ; use 2, 4 ; simp [h] ; absurd h ; aesop
--     · intro v v' t
--       fin_cases v <;> simp_all [Square]
--       · -- u=0, v=0 : goal ci-dessus
--         fin_cases v' <;> simp
--         · grind [Square] -- w=0 : pas de match possible
--         · by_cases h : t=1
--           · left ; simp [h] ; use 2, 2 ; simp
--           · left ; grind
--         · -- w=2 : voisin à t=2
--           by_cases h : t=2
--           · left ; simp only [h, Fin.isValue, forall_const] ; use 3, 3 ; simp
--           · left ; grind
--         · -- w=3 : voisin à t=3
--           by_cases h : t=3
--           · right ; intro x ; simp [h] ; omega
--           · left ; grind

-- lemma square_not_dis2'''' : ¬SubSquare.Dismountable2 := by
--   rw [isClique_notDismountable2_iff square_clique]
--   unfold SubSquare SubTempGraph.LatestNeighbor SubTempGraph.LatestEdge
--     SubTempGraph.EarliestNeigbhor SubTempGraph.EarliestEdge
--   simp only [toSubgraphTop, top_adj]
--   intro u
--   fin_cases u <;> simp only [Fin.zero_eta,Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
--   · right
--     constructor
--     · simp
--       intro v t hadj
--       fin_cases v <;> simp_all
--       · use 2, 3 ; grind [Square]
--       · use 3, 4 ; grind [Square]
--       · use 2, 4 ; grind [Square]
--     · intro β β' t t'
--       fin_cases β <;> simp only [Fin.zero_eta,Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
--       · fin_cases β' <;> simp only [Fin.zero_eta,Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
--         · grind [Square]
--         · by_cases h : t=1∧t'=1 <;> simp [h, Square]
--           · use 2,2 ; simp
--           · grind
--         · by_cases h : t=2∧t'=2 <;> simp [h, Square]
--           · use 3,3 ; simp
--           · grind
--         ·



-- lemma square_dis2 : SubSquare.Dismountable2
-- := by
--   unfold Dismountable2
--   simp only [square_clique, exists_and_left, true_and]
--   use 3
--   unfold SubTempGraph.LatestNeighbor SubTempGraph.LatestEdge SubTempGraph.EarliestNeigbhor SubTempGraph.EarliestEdge
--   simp [SubSquare, toSubgraphTop, top_adj]
--   constructor
--   · apply Or.inr

--   · apply Or.inl ; use 0, 3 ; constructor
--     · constructor ; trivial
--     · intro w t
--       match w, t with
--       | _, _ => grind [Square]
