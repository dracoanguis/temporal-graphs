/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Subgraph
import TemporalGraph.Bipartite
import TemporalGraph.Dismountability.Basic

/-!
# Worked Examples

This file contains worked examples of temporal graphs and their properties, including bipartite
examples: the bi-clique obtained by restricting `square` between two disjoint parts, and the
labelled complete bi-clique `biSquare`.
-/

open TemporalGraph

universe u

/-- A four-vertex temporal graph forming a square: edges at times 1, 2, 3, 4. -/
def square : TemporalGraph (Fin 4) := {
  Adj := fun v w t =>
    match t with
    | 1 => (v=0 ∧ w=1) ∨ (w=0 ∧ v=1)
    | 2 => (v=1 ∧ w=3) ∨ (w=1 ∧ v=3) ∨ (v=0 ∧ w=2) ∨ (w=0 ∧ v=2)
    | 3 => (v=0 ∧ w=3) ∨ (w=0 ∧ v=3) ∨ (v=1 ∧ w=2) ∨ (w=1 ∧ v=2)
    | 4 => (v=2 ∧ w=3) ∨ (w=2 ∧ v=3)
    | _ => False
}

instance square_isSymm : square.IsSymm := .of_adj (by
  intro n x y h
  simp only [square] at h ⊢
  split at h <;> aesop)

instance square_isLoopless : square.IsLoopless := ⟨fun t => ⟨fun x => by
  simp only [TemporalGraph.adjAt, square]
  split <;> aesop⟩⟩

/-- The square graph is a complete temporal clique. -/
lemma square_clique : square.IsCliqueGraph := by
  intro u _ v _ h
  match u, v with
  | 0, 1 => use 1 ; simp [square]
  | 1, 0 => use 1 ; simp [square]
  | 0, 2 => use 2 ; simp [square]
  | 2, 0 => use 2 ; simp [square]
  | 0, 3 => use 3 ; simp [square]
  | 1, 2 => use 3 ; simp [square]
  | 2, 1 => use 3 ; simp [square]
  | 1, 3 => use 2 ; simp [square]
  | 2, 3 => use 4 ; simp [square]
  | 3, 0 => use 3 ; simp [square]
  | 3, 1 => use 2 ; simp [square]
  | 3, 2 => use 4 ; simp [square]
  | 3, 3 => aesop_temporal_graph

private lemma square_adj_le {y z : Fin 4} {j : ℕ} (h : square.Adj y z j) : j ≤ 4 := by
  simp only [square] at h
  split at h <;> first | omega | exact h.elim

private lemma square_adj_pos {y z : Fin 4} {j : ℕ} (h : square.Adj y z j) : 1 ≤ j := by
  simp only [square] at h
  split at h <;> first | omega | exact h.elim

/-- Restricting the clique `square` to the edges between `{0, 1}` and `{2, 3}` gives a temporal
bi-clique `K₂,₂` — the shape of SAND 2025, Corollary 12. Here `{0, 1}` and `{2, 3}` are exactly
`V⁻` and `V⁺` (`square_vminus`, `square_vplus`). -/
theorem square_between_isBicliqueWith :
    (square.between {0, 1} {2, 3}).IsBicliqueWith {0, 1} {2, 3} :=
  IsClique.between_isBicliqueWith square_clique (Set.subset_univ _) (Set.subset_univ _)
    (Set.disjoint_left.mpr (by decide))

theorem square_vminus : (⊤ : square.Subgraph).vminus = {0, 1} := by
  ext x
  simp only [Subgraph.vminus, Set.mem_ofPred_eq, TemporalGraph.EarliestNeighbor,
    TemporalGraph.EarliestEdge, Subgraph.top_adj]
  constructor
  · rintro ⟨y, n, hadj, hmin⟩
    match y with
    | 0 =>
      have h1 := hmin 1 1 (by simp [square])
      interval_cases n <;> simp_all [square]
    | 1 =>
      have h1 := hmin 0 1 (by simp [square])
      interval_cases n <;> simp_all [square]
    | 2 =>
      have h1 := hmin 0 2 (by simp [square])
      interval_cases n <;> simp_all [square]
    | 3 =>
      have h1 := hmin 1 2 (by simp [square])
      interval_cases n <;> simp_all [square]
  · rintro (rfl | rfl)
    · exact ⟨1, 1, by simp [square], fun _ _ hadj ↦ square_adj_pos hadj⟩
    · exact ⟨0, 1, by simp [square], fun _ _ hadj ↦ square_adj_pos hadj⟩

theorem square_vplus : (⊤ : square.Subgraph).vplus = {2, 3} := by
  ext x
  simp only [Subgraph.vplus, Set.mem_ofPred_eq, TemporalGraph.LatestNeighbor,
    TemporalGraph.LatestEdge, Subgraph.top_adj]
  constructor
  · rintro ⟨y, n, hadj, hmax⟩
    have hup := square_adj_le hadj
    match y with
    | 0 =>
      have h1 := hmax 3 3 (by simp [square])
      interval_cases n <;> simp_all [square]
    | 1 =>
      have h1 := hmax 2 3 (by simp [square])
      interval_cases n <;> simp_all [square]
    | 2 =>
      have h1 := hmax 3 4 (by simp [square])
      interval_cases n; simp_all [square]
    | 3 =>
      have h1 := hmax 2 4 (by simp [square])
      interval_cases n; simp_all [square]
  · rintro (rfl | rfl)
    · exact ⟨3, 4, by simp [square], fun _ _ hadj ↦ square_adj_le hadj⟩
    · exact ⟨2, 4, by simp [square], fun _ _ hadj ↦ square_adj_le hadj⟩

/-- A temporal bi-clique `K₂,₂` with labels 1, 2, 3, 4. -/
def biSquare : TemporalGraph (Fin 2 ⊕ Fin 2) := completeBipartite fun a b ↦ 2 * a.val + b.val + 1

theorem biSquare_isBiclique : biSquare.IsBiclique Set.univ :=
  completeBipartite_isBiclique _

theorem biSquare_isHappy : biSquare.IsHappy :=
  ⟨completeBipartite_isSimple _, completeBipartite_isProper
    (fun a b b' h ↦ Fin.ext (by simpa using h))
    (fun b a a' h ↦ Fin.ext (by simpa using h))⟩

/-- The bridge in use: Mathlib's `SimpleGraph.IsBipartite` (2-colourability) for the footprint of
`biSquare`, obtained from the temporal bipartition. -/
theorem biSquare_simpleFootprint_isBipartite :
    (biSquare.simpleFootprint
      (completeBipartite_isSymm _) (completeBipartite_isLoopless _)).IsBipartite :=
  (isBipartite_iff_simpleFootprint _ _).mp
    ⟨_, _, (completeBipartite_isBicliqueWith _).isBipartiteWith⟩
