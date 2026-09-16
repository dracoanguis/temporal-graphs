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

/-- A loopless undirected temporal graph with edges only present at one time
(not proper or simple by definition) -/
@[ext, aesop safe constructors (rule_sets := [LooplessTemporalGraph])]
structure LooplessTemporalGraph (V : Type u) where
  /-- The adjacency labeled by a natural qualifying the time of existence -/
  Adj : V → V → ℕ → Prop
  symm : ∀ n : ℕ, Symmetric (fun x y => Adj x y n)
  loopless : ∀ n : ℕ, Std.Irrefl (fun x y => Adj x y n)



namespace LooplessTemporalGraph

variable {V : Type u}

@[simp]
protected theorem irrefl {G : LooplessTemporalGraph V} {x : V} {n : ℕ} : ¬G.Adj x x n :=
  (G.loopless n).irrefl x

section Adjacency

variable {G : LooplessTemporalGraph V} {x y : V} {n : ℕ}

theorem adj_comm (x y : V) (n : ℕ) : G.Adj x y n ↔ G.Adj y x n :=
  ⟨fun x => G.symm n x, fun x => G.symm n x⟩

@[symm]
theorem adj_symm (h : G.Adj x y n) : G.Adj y x n :=
  G.symm n h

theorem Adj.symm (h : G.Adj x y n) : G.Adj y x n :=
  G.symm n h

theorem ne_of_adj (h : G.Adj x y n) : x ≠ y := by
  rintro rfl
  exact G.irrefl h

protected theorem Adj.ne (h : G.Adj x y n) : x ≠ y :=
  G.ne_of_adj h

protected theorem Adj.ne' (h : G.Adj x y n) : y ≠ x :=
  h.ne.symm

end Adjacency

/-- The Footprint of a TemporalGraph is a SimpleGraph representing
the underlying edges unlabelled by time. -/
def Footprint (G : LooplessTemporalGraph V) : SimpleGraph V :=
  {
    Adj := fun x y => ∃ n, G.Adj x y n
    symm := by
      intro _ _ ⟨n, h⟩
      exact ⟨n, G.symm n h⟩
    loopless := ⟨fun _ ↦ by simp⟩
  }

def IsSimple (G : LooplessTemporalGraph V) : Prop :=
  ∀ (x y : V) (n m : ℕ), G.Adj x y n ∧ G.Adj x y m → n=m

def IsClique (G : LooplessTemporalGraph V) : Prop :=
  ∀ x y : V, x ≠ y → ∃ t, G.Adj x y t

lemma isClique_iff_footprint_isComplete {G : LooplessTemporalGraph V} :
    G.IsClique ↔ (Footprint G).IsClique Set.univ := by
  simp only [IsClique, ne_eq, SimpleGraph.IsClique, Set.Pairwise, Set.mem_univ, Footprint,
    forall_const]

def IsProper (G : LooplessTemporalGraph V) : Prop :=
  ∀ x y z : V, ∀ n : ℕ, G.Adj x y n ∧ G.Adj x z n → y = z

def IsHappy (G : LooplessTemporalGraph V) : Prop :=
  G.IsSimple ∧ G.IsProper

/-- The *earliest edge* of *x*, with *y* destination at *n* -/
def EarliestEdge (G : LooplessTemporalGraph V) (x y : V) (n : ℕ) : Prop :=
  G.Adj x y n ∧ ∀ z : V, ∀ j : ℕ, G.Adj x z j → n ≤ j

/-- The *latest edge* of *x*, with *y* destination at *n* -/
def LatestEdge (G : LooplessTemporalGraph V) (x y : V) (n : ℕ) : Prop :=
  G.Adj x y n ∧ ∀ z : V, ∀ j : ℕ, G.Adj x z j → j ≤ n

/-- *y* is an *earliest neighbor* of *x* -/
def EarliestNeighbor (G : LooplessTemporalGraph V) (x y : V) : Prop := ∃ n : ℕ, G.EarliestEdge x y n

/-- *y* is a *latest neighbor* of *x* -/
def LatestNeighbor (G : LooplessTemporalGraph V) (x y : V) : Prop := ∃ n : ℕ, G.LatestEdge x y n

section Order

def IsSubtempgraph {s : Set V} (G : LooplessTemporalGraph V) (H : LooplessTemporalGraph s) : Prop :=
  ∀ {x y : s} {n : ℕ}, H.Adj x y n → G.Adj ↑x ↑y n


-- Garder prime  et tierce et lemme equiv
variable {X Y : Type u}

def IsSubtempgraph' (f : X ↪ Y) (G : LooplessTemporalGraph X) (H : LooplessTemporalGraph Y) : Prop :=
  ∀ {x y : X} {n : ℕ}, G.Adj x y n → H.Adj (f x) (f y) n

def IsSubtempgraph'' [Coe X Y] (G : LooplessTemporalGraph X) (H : LooplessTemporalGraph Y) : Prop :=
  ∀ {x y : X} {n : ℕ}, G.Adj x y n → H.Adj x y n

def IsSubtempgraph''' {P : Y → Prop} (G : LooplessTemporalGraph {x : Y // P x})
  (H : LooplessTemporalGraph Y) : Prop :=
  ∀ {x y : {x : Y // P x}} {n : ℕ}, G.Adj x y n → H.Adj x y n

def IsSubtempgraph'''' {s : Set Y} (G : LooplessTemporalGraph s) (H : LooplessTemporalGraph Y) : Prop :=
  ∀ {x y : s} {n : ℕ}, G.Adj x y n → H.Adj ↑x ↑y n

example : ∀ (s : Set Y) (G : LooplessTemporalGraph s) (H : LooplessTemporalGraph Y),
  IsSubtempgraph''' G H ↔ IsSubtempgraph'''' G H := by
  intro s G H
  rfl

example : ∀ (s : Set Y) (G : LooplessTemporalGraph s) (H : LooplessTemporalGraph Y),
  @IsSubtempgraph'' _ _ (⟨ Subtype.val ⟩)  G H ↔ IsSubtempgraph'''' G H := by
  intro s G H
  rfl

example : ∀ (s : Set Y) (G : LooplessTemporalGraph s) (H : LooplessTemporalGraph Y),
  IsSubtempgraph' (⟨ Subtype.val, Subtype.val_injective ⟩)  G H ↔ IsSubtempgraph'''' G H := by
  intro s G H
  rfl

#print IsSubtempgraph'''

/-- This is a spanning SubTemporalGraph. -/
def IsSpanningSubTemporalGraph (G H : LooplessTemporalGraph V) : Prop :=
  ∀ {x y : V} {n : ℕ}, G.Adj x y n → H.Adj x y n

instance : LE (LooplessTemporalGraph V) :=
  ⟨IsSpanningSubTemporalGraph⟩

lemma le_iff_adj {G H : LooplessTemporalGraph V} :
    G ≤ H ↔ ∀ x y : V, ∀ n : ℕ, G.Adj x y n → H.Adj x y n :=
  .rfl

@[simp]
theorem isSpanningSubTemporalGraph_eq_le :
    (IsSpanningSubTemporalGraph : LooplessTemporalGraph V -> LooplessTemporalGraph V -> Prop) =
    (· ≤ ·) :=
  rfl

instance : Bot (LooplessTemporalGraph V) where
  bot := {
    Adj _ _ _ := False
    symm := by
      intro _ _ _ h
      trivial
    loopless := by
      intro _
      exact ⟨fun _ ↦ by simp⟩
  }

end Order

section NeighborhoodSet


def NeighborhoodSet (G : LooplessTemporalGraph V) (x : V) := {y | ∃ n : ℕ, G.Adj x y n}

@[simp]
theorem mem_neighborSet (G : LooplessTemporalGraph V) (x y : V) :
    y ∈ G.NeighborhoodSet x ↔ ∃ n : ℕ, G.Adj x y n :=
  Iff.rfl

-- instance NeighborSet.memDecidable (G : LooplessTemporalGraph V) (v : V)
-- [DecidableRel (λ x y↦ ∃ t, G.Adj x y t)] :
    -- DecidablePred (· ∈ G.NeighborSet v) :=
  -- inferInstanceAs <| DecidablePred (Adj G v)

end NeighborhoodSet

section EdgeSet

/-- The set of every edges in G. -/
def EdgeSet (G : LooplessTemporalGraph V) : Set ((Sym2 V) × ℕ) :=
  {(p, n) | ∃ x y : p, G.Adj x y n}

@[simp]
theorem mem_edgeSet (G : LooplessTemporalGraph V) {x y : V} {n : ℕ} :
    (s(x,y), n) ∈ G.EdgeSet ↔ G.Adj x y n := by
  apply Iff.intro
  · intro ⟨u, v, hadj⟩
    rcases Sym2.mem_iff.mp u.prop with heq | heq
    <;> rw [heq] at hadj
    · have heq' := Sym2.mem_iff.mp v.prop |>.resolve_left hadj.ne'
      rw [heq'] at hadj
      exact hadj
    · have heq' := Sym2.mem_iff.mp v.prop |>.resolve_right hadj.ne'
      rw [heq'] at hadj
      exact hadj.symm
  · intro hadj
    have hin : x ∈ s(x,y) := Sym2.mem_iff.mpr <| Or.inl <| Eq.refl x
    have hin' : y ∈ s(x,y) := Sym2.mem_iff.mpr <| Or.inr <| Eq.refl y
    exact ⟨⟨x, hin⟩, ⟨⟨y, hin'⟩, hadj⟩⟩

end EdgeSet

section Size

def size (G : LooplessTemporalGraph V) [Fintype G.EdgeSet] := Fintype.card G.EdgeSet

end Size

end LooplessTemporalGraph
