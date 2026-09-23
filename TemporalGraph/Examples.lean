/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Subgraph

/-!
# Worked Examples

This file contains worked examples of temporal graphs and their properties.
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

instance square_isSymm : square.IsSymm := ⟨by
  intro n x y h
  simp only [square] at h ⊢
  split at h <;> aesop⟩

instance square_isLoopless : square.IsLoopless := ⟨fun t => by
  simp only [square]
  split <;> constructor <;> aesop⟩

/-- The square graph is a complete temporal clique. -/
lemma square_clique : square.IsClique
:= by
  intro u v _
  match u, v with
  | 0, 1 => simp [square] ; use 1
  | 1, 0 => simp [square] ; use 1
  | 0, 2 => use 2 ; simp [square]
  | 2, 0 => use 2 ; simp [square]
  | 0, 3 => use 3 ; simp [square]
  | 1, 2 => use 3 ; simp [square]
  | 2, 1 => use 3 ; simp [square]
  | 1, 3 => use 2 ; simp [square]
  | 2, 3 => use 4 ; simp [square]
  | 3, 0 => simp [square] ; use 3
  | 3, 1 => simp [square] ; use 2
  | 3, 2 => simp [square] ; use 4
  | 3, 3 => aesop_temporal_graph
