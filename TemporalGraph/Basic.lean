/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Init
import Mathlib


macro (name := aesop_temporal_graph) "aesop_temporal_graph" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c*
      (config := { introsTransparency? := some .default, terminal := true })
      (rule_sets := [$(Lean.mkIdent `LooplessTemporalGraph):ident]))



universe u

/-- A temporal graph: edges are labeled by the time (ℕ) at which they exist.
No symmetry or irreflexivity is required — see `IsSymm` and `IsLoopless`. -/
@[ext, aesop safe constructors (rule_sets := [LooplessTemporalGraph])]
structure TemporalGraph (V : Type u) where
  /-- The adjacency labeled by a natural qualifying the time of existence -/
  Adj : V → V → ℕ → Prop



namespace TemporalGraph

variable {V : Type u}

def IsSymm (G : TemporalGraph V) : Prop :=
  ∀ n : ℕ, Symmetric (fun x y => G.Adj x y n)

def IsLoopless (G : TemporalGraph V) : Prop :=
  ∀ n : ℕ, Std.Irrefl (fun x y => G.Adj x y n)

@[simp]
protected theorem irrefl {G : TemporalGraph V} (hl : G.IsLoopless) {x : V} {n : ℕ} : ¬G.Adj x x n :=
  (hl n).irrefl x

section Adjacency

variable {G : TemporalGraph V} {x y : V} {n : ℕ}

theorem adj_comm (hs : G.IsSymm) (x y : V) (n : ℕ) : G.Adj x y n ↔ G.Adj y x n :=
  ⟨fun x => hs n x, fun x => hs n x⟩

@[symm]
theorem adj_symm (hs : G.IsSymm) (h : G.Adj x y n) : G.Adj y x n :=
  hs n h

theorem Adj.symm (hs : G.IsSymm) (h : G.Adj x y n) : G.Adj y x n :=
  hs n h

theorem ne_of_adj (hl : G.IsLoopless) (h : G.Adj x y n) : x ≠ y := by
  rintro rfl
  exact G.irrefl hl h

protected theorem Adj.ne (hl : G.IsLoopless) (h : G.Adj x y n) : x ≠ y :=
  G.ne_of_adj hl h

protected theorem Adj.ne' (hl : G.IsLoopless) (h : G.Adj x y n) : y ≠ x :=
  (h.ne hl).symm

end Adjacency

/-- The Footprint of a TemporalGraph is a Digraph representing the underlying
directed edges unlabelled by time. -/
def Footprint (G : TemporalGraph V) : Digraph V :=
  { Adj := fun x y => ∃ n, G.Adj x y n }

def IsSimple (G : TemporalGraph V) : Prop :=
  ∀ (x y : V) (n m : ℕ), G.Adj x y n ∧ G.Adj x y m → n=m

def IsClique (G : TemporalGraph V) : Prop :=
  ∀ x y : V, x ≠ y → ∃ t, G.Adj x y t

lemma isClique_iff_footprint_isComplete {G : TemporalGraph V} :
    G.IsClique ↔ Set.univ.Pairwise G.Footprint.Adj := by
  simp only [IsClique, ne_eq, Set.Pairwise, Set.mem_univ, Footprint, forall_const]

def IsProper (G : TemporalGraph V) : Prop :=
  ∀ x y z : V, ∀ n : ℕ, G.Adj x y n ∧ G.Adj x z n → y = z

def IsHappy (G : TemporalGraph V) : Prop :=
  G.IsSimple ∧ G.IsProper

/-- The *earliest edge* of *x*, with *y* destination at *n* -/
def EarliestEdge (G : TemporalGraph V) (x y : V) (n : ℕ) : Prop :=
  G.Adj x y n ∧ ∀ z : V, ∀ j : ℕ, G.Adj x z j → n ≤ j

/-- The *latest edge* of *x*, with *y* destination at *n* -/
def LatestEdge (G : TemporalGraph V) (x y : V) (n : ℕ) : Prop :=
  G.Adj x y n ∧ ∀ z : V, ∀ j : ℕ, G.Adj x z j → j ≤ n

/-- *y* is an *earliest neighbor* of *x* -/
def EarliestNeighbor (G : TemporalGraph V) (x y : V) : Prop := ∃ n : ℕ, G.EarliestEdge x y n

/-- *y* is a *latest neighbor* of *x* -/
def LatestNeighbor (G : TemporalGraph V) (x y : V) : Prop := ∃ n : ℕ, G.LatestEdge x y n

section Order

variable {X Y : Type u}

/-- `G` is a sub-temporal-graph of `H`, embedded via the injection `f`. -/
def IsSubtempgraph' (f : X ↪ Y) (G : TemporalGraph X) (H : TemporalGraph Y) : Prop :=
  ∀ {x y : X} {n : ℕ}, G.Adj x y n → H.Adj (f x) (f y) n

/-- `G`, a temporal graph on the vertices of `Y` satisfying `P`, is a
sub-temporal-graph of `H`. -/
def IsSubtempgraph {P : Y → Prop} (G : TemporalGraph {x : Y // P x})
    (H : TemporalGraph Y) : Prop :=
  ∀ {x y : {x : Y // P x}} {n : ℕ}, G.Adj x y n → H.Adj x y n

/-- This is a spanning SubTemporalGraph. -/
def IsSpanningSubTemporalGraph (G H : TemporalGraph V) : Prop :=
  ∀ {x y : V} {n : ℕ}, G.Adj x y n → H.Adj x y n

instance : LE (TemporalGraph V) :=
  ⟨IsSpanningSubTemporalGraph⟩

lemma le_iff_adj {G H : TemporalGraph V} :
    G ≤ H ↔ ∀ x y : V, ∀ n : ℕ, G.Adj x y n → H.Adj x y n :=
  .rfl

@[simp]
theorem isSpanningSubTemporalGraph_eq_le :
    (IsSpanningSubTemporalGraph : TemporalGraph V -> TemporalGraph V -> Prop) =
    (· ≤ ·) :=
  rfl

instance : Bot (TemporalGraph V) where
  bot := { Adj _ _ _ := False }

end Order

section NeighborhoodSet


def NeighborhoodSet (G : TemporalGraph V) (x : V) := {y | ∃ n : ℕ, G.Adj x y n}

@[simp]
theorem mem_neighborSet (G : TemporalGraph V) (x y : V) :
    y ∈ G.NeighborhoodSet x ↔ ∃ n : ℕ, G.Adj x y n :=
  Iff.rfl

-- instance NeighborSet.memDecidable (G : TemporalGraph V) (v : V)
-- [DecidableRel (λ x y↦ ∃ t, G.Adj x y t)] :
    -- DecidablePred (· ∈ G.NeighborSet v) :=
  -- inferInstanceAs <| DecidablePred (Adj G v)

end NeighborhoodSet

section EdgeSet

/-- The set of every edges in G. -/
def EdgeSet (G : TemporalGraph V) : Set ((Sym2 V) × ℕ) :=
  {(p, n) | ∃ x y : p, G.Adj x y n}

@[simp]
theorem mem_edgeSet (G : TemporalGraph V) (hs : G.IsSymm) (hl : G.IsLoopless) {x y : V} {n : ℕ} :
    (s(x,y), n) ∈ G.EdgeSet ↔ G.Adj x y n := by
  apply Iff.intro
  · intro ⟨u, v, hadj⟩
    rcases Sym2.mem_iff.mp u.prop with heq | heq
    <;> rw [heq] at hadj
    · have heq' := Sym2.mem_iff.mp v.prop |>.resolve_left (hadj.ne' hl)
      rw [heq'] at hadj
      exact hadj
    · have heq' := Sym2.mem_iff.mp v.prop |>.resolve_right (hadj.ne' hl)
      rw [heq'] at hadj
      exact hadj.symm hs
  · intro hadj
    have hin : x ∈ s(x,y) := Sym2.mem_iff.mpr <| Or.inl <| Eq.refl x
    have hin' : y ∈ s(x,y) := Sym2.mem_iff.mpr <| Or.inr <| Eq.refl y
    exact ⟨⟨x, hin⟩, ⟨⟨y, hin'⟩, hadj⟩⟩

end EdgeSet

section Size

def size (G : TemporalGraph V) [Fintype G.EdgeSet] := Fintype.card G.EdgeSet

end Size

end TemporalGraph
