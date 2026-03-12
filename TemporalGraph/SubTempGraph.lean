/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.TemporalWalk
import TemporalGraph.Maps

universe u

namespace SimpleTemporalGraph


@[ext]
structure SubTempGraph {V : Type u} (G : SimpleTemporalGraph V) where
  Verts : Set V
  Adj : V → V → ℕ → Prop

  adj_sub : ∀ {x y : V} {n : ℕ}, Adj x y n → G.Adj x y n
  edge_vert : ∀ {x y : V} {n : ℕ}, Adj x y n → x ∈ Verts
  symm : ∀ n, Symmetric (fun x y => Adj x y n)

namespace SubTempGraph

variable {V : Type u} {G : SimpleTemporalGraph V}

-- protected def mk' {s : Set V} (G' : SimpleTemporalGraph s) (h : G.IsSubtempgraph G')
-- : SubTempGraph G
-- := {
  -- Verts := s
  -- Adj := fun x y n => ∃ hx : x ∈ s, ∃ hy : y ∈ s, G'.Adj ⟨x, hx⟩ ⟨y, hy⟩ n,

  -- adj_sub := by
    -- intro _ _ _ h'
    -- rcases h' with ⟨_, _, h'⟩
    -- exact h h'

  -- edge_vert := by
    -- intro _ _ _ h
    -- rcases h with ⟨h', _, _⟩
    -- exact h'

  -- symm := by
    -- intro n _ _ h'
    -- rcases h' with ⟨hx, hy, h'⟩
    -- exact ⟨hy, hx, G'.symm n h' ⟩
-- }

protected theorem loopless (G' : SubTempGraph G) : ∀ n, Std.Irrefl (fun x y ↦ G'.Adj x y n) :=
  fun _ ↦ ⟨fun _ h ↦ G.irrefl (G'.adj_sub h)⟩

@[simp]
protected theorem irrefl {G' : SubTempGraph G} {x : V} {n : ℕ} : ¬G'.Adj x x n :=
  (G'.loopless n).irrefl x

theorem adj_comm (G' : SubTempGraph G) (x y : V) (n : ℕ) : G'.Adj x y n ↔ G'.Adj y x n :=
  ⟨fun x ↦ G'.symm n x, fun x ↦ G'.symm n x⟩

@[symm]
theorem adj_symm (G' : SubTempGraph G) {x y : V} {n : ℕ} (h : G'.Adj x y n) : G'.Adj y x n :=
  G'.symm n h

protected theorem Adj.symm {H : SubTempGraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.Adj y x n :=
  H.symm n h

protected theorem Adj.adj_sub {H : G.SubTempGraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    G.Adj u v t :=
  H.adj_sub h

protected theorem Adj.fst_mem {H : G.SubTempGraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    u ∈ H.Verts :=
  H.edge_vert h

protected theorem Adj.snd_mem {H : G.SubTempGraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    y ∈ H.Verts :=
  h.symm.fst_mem

-- protected theorem Adj.ne {H : G.SubTemporalGraph} {u v : V} {t : ℕ} (h : H.Adj u v t)
-- : u ≠ v
-- := h.adj_sub.ne

/-- Coercion from `H : SubTemporalGraph G` to a `SimpleTemporalGraph H.Verts`. -/
@[simps, coe]
protected def coe (H : SubTempGraph G) : SimpleTemporalGraph H.Verts where
  Adj x y n := H.Adj x y n
  symm n _ _ h := H.symm n h
  loopless _ := ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩

-- Seems a bit weird for it to work should check on site
instance {V : Type u} {G : SimpleTemporalGraph V} {G' : SubTempGraph G}
: Coe (SubTempGraph G) (SimpleTemporalGraph G'.Verts) where
  coe H := {
    Adj v w t := H.Adj v w t
    symm t _ _ h := H.symm t h
    loopless _ := ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩
  }

@[simp]
theorem Adj.adj_sub' (H : SubTempGraph G) (x y : H.Verts) (n : ℕ) (h : H.Adj x y n) :
    G.Adj x y n :=
  H.adj_sub h

theorem coe_adj_sub (H : SubTempGraph G) (x y : H.Verts) (n : ℕ) (h : H.coe.Adj x y n) :
    G.Adj x y n :=
  H.adj_sub h

-- Given `h : H.Adj u v t`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩ t`.
protected theorem Adj.coe {H : G.SubTempGraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.coe.Adj ⟨x, h.fst_mem⟩ ⟨y, h.snd_mem⟩ n :=
  h

-- instance (G : SimpleGraph V) (H : SubTempGraph G) [DecidableRel H.Adj]
-- : DecidableRel H.coe.Adj
-- := fun a b ↦ ‹DecidableRel H.Adj› _ _

theorem coe_sub (H : SubTempGraph G) : G.IsSubtempgraph H.coe := by
  rw [SimpleTemporalGraph.IsSubtempgraph]
  intro x y n
  exact coe_adj_sub H x y n

section Spanning

/-- A SubTempGraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (H : SubTempGraph G) : Prop :=
  ∀ x : V, x ∈ H.Verts

theorem isSpanning_iff {H : SubTempGraph G} : H.IsSpanning ↔ H.Verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

/-- Coercion from `SubTempGraph G` to `SimpleTemporalGraph V`.  If `H` is a spanning
subgraph, then `H.spanningCoe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
protected def spanningCoe (H : SubTempGraph G) : SimpleTemporalGraph V where
  Adj := H.Adj
  symm := H.symm
  loopless := H.loopless

theorem Adj.of_spanningCoe {H : SubTempGraph G} {x y : H.Verts} {n : ℕ}
    (h : H.spanningCoe.Adj x y n) : G.Adj x y n :=
  H.adj_sub h

lemma spanningcoe_le (H : SubTempGraph G) : H.spanningCoe ≤ G := H.adj_sub

variable {H₁ : SubTempGraph G} {H₂ : SubTempGraph G}

theorem spanningCoe_inj : H₁.spanningCoe = H₂.spanningCoe ↔ H₁.Adj = H₂.Adj := by
  simp [SubTempGraph.spanningCoe]

end Spanning

section Props

def IsClique (H : SubTempGraph G) : Prop := ∀ (x y : H.Verts), x ≠ y → ∃ n, H.Adj x y n

def IsProper (H : SubTempGraph G) : Prop := ∀ (x y z : V) (n : ℕ), H.Adj x y n ∧ H.Adj x z n → y=z

-- From SimpleGraph.Subgraph.IsMatching
def IsMatching (M : SubTempGraph G) : Prop := ∀ ⦃v : V⦄, v ∈ M.Verts → ∃! w , ∃ t, M.Adj v w t

-- From SimpleGraph.Subgraph.IsPerfectMatching
def IsPerfectMatching (M : SubTempGraph G) := M.IsMatching ∧ M.IsSpanning

end Props

section Order

instance : Top G.SubTempGraph where
  top := {
    Verts := Set.univ
    Adj := G.Adj
    adj_sub := id
    symm := G.symm
    edge_vert := @fun x _ _ _ ↦ Set.mem_univ x
  }

@[simp]
theorem top_adj {x y : V} {n : ℕ} : (⊤ : SubTempGraph G).Adj x y n ↔ G.Adj x y n :=
  Iff.rfl

theorem top_verts : (⊤ : SubTempGraph G).Verts = Set.univ := rfl

theorem top_spanningCoe : (⊤ : SubTempGraph G).spanningCoe = G := rfl

instance : Bot G.SubTempGraph where
  bot := {
    Verts := ∅
    Adj := ⊥
    adj_sub := False.elim
    edge_vert := False.elim
    symm _ _ _ := id
  }

def IsSubgraphOf (H : SubTempGraph G) (H' : SubTempGraph G) : Prop :=
  (H.Verts ⊆ H'.Verts)
  ∧
  (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n)

instance : LE (SubTempGraph G) :=
  ⟨IsSubgraphOf⟩

instance : BoundedOrder (SubTempGraph G) where
  top := ⊤
  bot := ⊥
  le_top x := ⟨Set.subset_univ _, by intro _ _ _ h ; rw [top_adj] ; exact x.adj_sub h⟩
  bot_le _ := ⟨Set.empty_subset _, False.elim⟩

instance : LT (SubTempGraph G) where
  lt H H' :=
    ((H.Verts ⊂ H'.Verts) ∧ (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n))
    ∨
    ((H.Verts = H'.Verts) ∧ (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n)
      ∧ (∃ (x y : V) (n : ℕ), H'.Adj x y n ∧ ¬ H.Adj x y n))

instance : Preorder (SubTempGraph G) where
  le_refl H := ⟨by simp, by simp⟩
  le_trans A B C h h' := ⟨h.left.trans h'.left , by
    intro _ _ _ hadj
    exact h'.right <| h.right hadj
  ⟩
  lt_iff_le_not_ge A B := by
    constructor
    · intro h ; constructor
      · apply h.elim
        · intro h' ; exact ⟨h'.left.subset, h'.right⟩
        · intro h' ; exact ⟨h'.left.subset, h'.right.left⟩
      · apply h.elim
        · intro h h' ; apply h'.left.not_ssubset ; exact h.left
        · intro h h' ; have ⟨x, y, t, hB, hnA⟩ := h.right.right ; apply hnA.elim ; exact h'.right hB
    · intro h ; apply h.left.left.eq_or_ssubset.elim
      · intro h' ; right ; constructor
        · assumption
        · constructor
          · exact h.left.right
          · have h := h.right ; dsimp [LE.le, IsSubgraphOf] at h ; push_neg at h
            exact h h'.symm.subset
      · intro h' ; left ; constructor
        · assumption
        · exact h.left.right

instance : PartialOrder (SubTempGraph G) where
  le_antisymm A B h h' := by
    ext _ _ _
    · constructor
      · intro h'' ; apply h.left ; assumption
      · intro h'' ; apply h'.left ; assumption
    · exact ⟨h.right, h'.right⟩

end Order

section Induce

/-- A SubTempGraph is called an *induced SubTempGraph* if vertices of `H` are adjacent if
they are adjacent in `G`. -/
def IsInduced (H : SubTempGraph G) : Prop :=
  ∀ ⦃x⦄, x ∈ H.Verts → ∀ ⦃y⦄, y ∈ H.Verts → ∀ n : ℕ, G.Adj x y n → H.Adj x y n

@[simp] lemma IsInduced.top : (⊤ : G.SubTempGraph).IsInduced := fun _ _ _ _ _ ↦ id

@[simps]
def induce (H : G.SubTempGraph) (s : Set V) : G.SubTempGraph where
  Verts := s
  Adj x y n := x ∈ s ∧ y ∈ s ∧ H.Adj x y n
  adj_sub h := H.adj_sub h.2.2
  edge_vert h := h.1
  symm n _ _ h := ⟨h.2.1, h.1, H.symm n h.2.2⟩

end Induce

section DeleteVerts

abbrev deleteVerts (H : SubTempGraph G) (s : Set V) : G.SubTempGraph :=
  H.induce (H.Verts \ s)

lemma deleteVerts_verts (H : SubTempGraph G) (s : Set V) : (H.deleteVerts s).Verts = H.Verts \ s :=
  rfl

theorem deleteVerts_le {H : SubTempGraph G} {s : Set V} : (H.deleteVerts s) ≤ H := by
  constructor <;> simp [Set.diff_subset]

theorem deleteVerts_le' (H : SubTempGraph G) (s : Set V) : (H.deleteVerts s) ≤ H := by
  constructor <;> simp [Set.diff_subset]


end DeleteVerts

section AddVerts

abbrev addVerts (H : SubTempGraph G) (s : Set V) : G.SubTempGraph :=
  H.induce (H.Verts ∪ s)

lemma addVerts_verts (H : SubTempGraph G) (s : Set V) : (H.addVerts s).Verts = H.Verts ∪ s :=
  rfl

lemma addVerts_Adj {x y : V} {n : ℕ} {H : SubTempGraph G} {s : Set V} :
    H.Adj x y n → (H.addVerts s).Adj x y n := by
  have hinc : H.Verts ⊆ (H.addVerts s).Verts := by simp
  intro h
  have hin := hinc <| H.edge_vert h
  have hin' := hinc <| H.edge_vert h.symm
  exact ⟨hin, hin', h⟩

lemma addVerts_le {H : SubTempGraph G} {s : Set V} : H ≤ (H.addVerts s) := by
  constructor
  · simp
  · intro _ _ _ h ; exact addVerts_Adj h

lemma addVerts_le' (H : SubTempGraph G) (s : Set V) : H ≤ (H.addVerts s) := addVerts_le

end AddVerts

section AddEdge

variable {x y : V} {n : ℕ}

def addEdge (H : SubTempGraph G) (h : G.Adj x y n) (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    SubTempGraph G where
  Verts := H.Verts
  Adj x' y' n' := H.Adj x' y' n' ∨ (x'=x∧y'=y∧n'=n) ∨ (y'=x∧x'=y∧n'=n)

  symm := by
    intro m _ _ h
    apply h.elim3
    · intro h ; exact Or.inl <| H.symm m h
    · intro h ; exact Or.inr <| Or.inr h
    · intro h ; exact Or.inr <| Or.inl h

  edge_vert := by
    intro _ _ _ hadj
    apply hadj.elim3
    · intro h ; exact H.edge_vert h
    · intro h'' ; rw [h''.left.symm] at h₁ ; exact h₁.left
    · intro h'' ; rw [h''.right.left.symm] at h₁ ; exact h₁.right

  adj_sub := by
    intro _ _ _ h''
    apply h''.elim3
    · intro h'' ; exact H.adj_sub h''
    · intro h'' ; rwa [h''.left.symm, h''.right.left.symm, h''.right.right.symm] at h
    · intro h'' ; rw [h''.left.symm, h''.right.left.symm, h''.right.right.symm] at h ; exact h.symm

variable {H : SubTempGraph G} {h : G.Adj x y n} {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts}

theorem addEdge_le : H ≤ addEdge H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

theorem addEdge_le' (H : SubTempGraph G) (h : G.Adj x y n) (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    H ≤ addEdge H h h₁ :=
  addEdge_le

theorem addEdge_edge : (addEdge H h h₁).Adj x y n := by
  right
  left
  exact ⟨rfl, rfl, rfl⟩

theorem addEdge_verts : (addEdge H h h₁).Verts = H.Verts := rfl

end AddEdge

section EdgeProps

variable {x y : V} {n : ℕ}

def EarliestEdge (H : SubTempGraph G) (x y : V) (n : ℕ) : Prop :=
  H.Adj x y n ∧ ∀ (z : V) (m : ℕ), H.Adj x z m → n ≤ m

def LatestEdge (H : SubTempGraph G) (x y : V) (n : ℕ) : Prop :=
  H.Adj x y n ∧ ∀ (z : V) (m : ℕ), H.Adj x z m → m ≤ n

def EarliestNeighbor (H : SubTempGraph G) (x y : V) : Prop := ∃ n, H.EarliestEdge x y n

def LatestNeighbor (H : SubTempGraph G) (x y : V) : Prop := ∃ n, H.LatestEdge x y n

lemma earliestEdge_exists {H : SubTempGraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    ∃ (z : V) (m : ℕ), H.EarliestEdge x z m := by
  sorry

lemma latestEdge_exists {H : SubTempGraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    ∃ (z : V) (m : ℕ), H.LatestEdge x z m := by
  sorry

lemma subgraph_earliestEdge_of_graph_earliestEdge {H : SubTempGraph G}
    (h : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.EarliestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert h₁.symm⟩ n := by
  constructor
  · exact h₁
  · rw [SimpleTemporalGraph.EarliestEdge] at h
    rcases h with ⟨hαβ, hmin⟩
    intro z m hadj
    cases z with
    | mk z hz => exact hmin z m <| H.adj_sub hadj

lemma subgraph_latestEdge_of_graph_latestEdge {H : SubTempGraph G}
    (h : G.LatestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.LatestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert h₁.symm⟩ n := by
  constructor
  · exact h₁
  · rw [SimpleTemporalGraph.LatestEdge] at h
    rcases h with ⟨_, hmin⟩
    intro z m hadj
    cases z with
    | mk z hz => exact hmin z m <| H.adj_sub hadj

end EdgeProps

section Maps

section Iso

variable {V W : Type*} {G : SimpleTemporalGraph V} {H : SimpleTemporalGraph W}

/-- WIP consider removing as it is not used -/
abbrev Iso (G' : SubTempGraph G) (H' : SubTempGraph H)
:= G'.coe ≃tg H'.coe

@[inherit_doc] infixl:50 " ≃stg " => Iso

end Iso

end Maps

section NeighborSet

def NeighborSet (H : SubTempGraph G) (x : V) := {y | ∃ n, H.Adj x y n}

theorem mem_neighborSet (H : SubTempGraph G) (x y : V) : y ∈ H.NeighborSet x ↔ ∃ n, H.Adj x y n :=
  Iff.rfl

theorem neighborSet_top (v : V) : (⊤ : G.SubTempGraph).NeighborSet v = G.NeighborSet v := rfl

theorem neighborSet_subset_verts (H : SubTempGraph G) (x : V) : H.NeighborSet x ⊆ H.Verts := by
  intro _ h
  rw [mem_neighborSet] at h
  let ⟨_, h⟩ := h
  exact H.edge_vert <| H.adj_symm h

end NeighborSet

end SubTempGraph

namespace NonemptyTemporalWalk

variable {V : Type u} {G : SimpleTemporalGraph V} {H : SubTempGraph G}

@[coe]
protected def lift_subtempgraph_walk {x y : H.Verts} {n m : ℕ} :
    H.coe.NonemptyTemporalWalk x n y m → G.NonemptyTemporalWalk ↑x n ↑y m
  | Single h => Single (H.adj_sub h)
  | Step h p h' =>
    Step (H.adj_sub h)
      (p.lift_subtempgraph_walk)
      h'

instance {x y : H.Verts} {n m : ℕ} : Coe (H.coe.NonemptyTemporalWalk x n y m)
    (G.NonemptyTemporalWalk ↑x n ↑y m) where
  coe := NonemptyTemporalWalk.lift_subtempgraph_walk

@[coe]
protected def lift_subtempgraph_walk' {H' : SubTempGraph G} {x y : H.Verts} {n m : ℕ} (h : H ≤ H') :
    H.coe.NonemptyTemporalWalk x n y m → H'.coe.NonemptyTemporalWalk
      ⟨x, Set.mem_of_subset_of_mem h.left x.prop⟩ n
      ⟨y, Set.mem_of_subset_of_mem h.left y.prop⟩ m
  | Single h' => Single (h.right h')
  | Step h' p hle =>
    Step (h.right h').coe
      (NonemptyTemporalWalk.lift_subtempgraph_walk' h p)
      hle

end NonemptyTemporalWalk

namespace TemporalWalk

variable {V : Type u} {G : SimpleTemporalGraph V} {H : SubTempGraph G}

@[coe]
protected def lift_subtempgraph_walk {x y : H.Verts} {n m : ℕ} :
    H.coe.TemporalWalk x n y m → G.TemporalWalk ↑x n ↑y m
  | Empty => Empty
  | Nonempty p => Nonempty ↑p

instance {x y : H.Verts} {n m : ℕ} : Coe (H.coe.TemporalWalk x n y m)
    (G.TemporalWalk ↑x n ↑y m) where
  coe := TemporalWalk.lift_subtempgraph_walk

@[coe]
protected def lift_subtempgraph_walk' {H' : SubTempGraph G} {x y : H.Verts} {n m : ℕ} (h : H ≤ H') :
    H.coe.TemporalWalk x n y m → H'.coe.TemporalWalk
      ⟨x, Set.mem_of_subset_of_mem h.left x.prop⟩ n
      ⟨y, Set.mem_of_subset_of_mem h.left y.prop⟩ m
  | Empty => Empty
  | Nonempty p => Nonempty <| p.lift_subtempgraph_walk' h

end TemporalWalk

section SubgraphProps

variable {V : Type u} {G : SimpleTemporalGraph V}

@[simps]
def toSubgraph (H : SimpleTemporalGraph V) (h : H ≤ G) : G.SubTempGraph where
  Verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  symm _ := H.symm _

theorem toSubgraph.isSpanning (H : SimpleTemporalGraph V) (h : H ≤ G) :
    (toSubgraph H h).IsSpanning :=
  Set.mem_univ

def toSubgraphTop : G.SubTempGraph := ⊤

end SubgraphProps

end SimpleTemporalGraph
