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
structure SubTemporalGraph {V : Type u} (G : SimpleTemporalGraph V) where
  Verts : Set V
  Adj : V → V → ℕ → Prop

  adj_sub : ∀ {x y : V} {n : ℕ}, Adj x y n → G.Adj x y n
  edge_vert : ∀ {x y : V} {n : ℕ}, Adj x y n → x ∈ Verts
  symm : ∀ n, Symmetric (fun x y => Adj x y n)

namespace SubTemporalGraph

variable {V : Type u} {G : SimpleTemporalGraph V}

-- protected def mk' {s : Set V} (G' : SimpleTemporalGraph s) (h : G.IsSubtempgraph G')
-- : SubTemporalGraph G
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

protected theorem loopless (H : SubTemporalGraph G) : ∀ n, Std.Irrefl (fun x y ↦ H.Adj x y n) :=
  fun _ ↦ ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩

@[simp]
protected theorem irrefl {H : SubTemporalGraph G} {x : V} {n : ℕ} : ¬H.Adj x x n :=
  (H.loopless n).irrefl x

theorem adj_comm (H : SubTemporalGraph G) (x y : V) (n : ℕ) : H.Adj x y n ↔ H.Adj y x n :=
  ⟨fun x ↦ H.symm n x, fun x ↦ H.symm n x⟩

@[symm]
theorem adj_symm (H : SubTemporalGraph G) {x y : V} {n : ℕ} (h : H.Adj x y n) : H.Adj y x n :=
  H.symm n h

protected theorem Adj.symm {H : SubTemporalGraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.Adj y x n :=
  H.symm n h

protected theorem Adj.adj_sub {H : G.SubTemporalGraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    G.Adj u v t :=
  H.adj_sub h

protected theorem Adj.fst_mem {H : G.SubTemporalGraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    u ∈ H.Verts :=
  H.edge_vert h

protected theorem Adj.snd_mem {H : G.SubTemporalGraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    y ∈ H.Verts :=
  h.symm.fst_mem

-- protected theorem Adj.ne {H : G.SubTemporalGraph} {u v : V} {t : ℕ} (h : H.Adj u v t)
-- : u ≠ v
-- := h.adj_sub.ne

/-- Coercion from `H : SubTemporalGraph G` to a `SimpleTemporalGraph H.Verts`. -/
@[simps, coe]
protected def coe (H : SubTemporalGraph G) : SimpleTemporalGraph H.Verts where
  Adj x y n := H.Adj x y n
  symm n _ _ h := H.symm n h
  loopless _ := ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩

-- Seems a bit weird for it to work should check on site
instance {V : Type u} {G : SimpleTemporalGraph V} {G' : SubTemporalGraph G}
: Coe (SubTemporalGraph G) (SimpleTemporalGraph G'.Verts) where
  coe H := {
    Adj v w t := H.Adj v w t
    symm t _ _ h := H.symm t h
    loopless _ := ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩
  }

@[simp]
theorem Adj.adj_sub' (H : SubTemporalGraph G) (x y : H.Verts) (n : ℕ) (h : H.Adj x y n) :
    G.Adj x y n :=
  H.adj_sub h

theorem coe_adj_sub (H : SubTemporalGraph G) (x y : H.Verts) (n : ℕ) (h : H.coe.Adj x y n) :
    G.Adj x y n :=
  H.adj_sub h

-- Given `h : H.Adj u v t`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩ t`.
protected theorem Adj.coe {H : G.SubTemporalGraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.coe.Adj ⟨x, h.fst_mem⟩ ⟨y, h.snd_mem⟩ n :=
  h

-- instance (G : SimpleGraph V) (H : SubTemporalGraph G) [DecidableRel H.Adj]
-- : DecidableRel H.coe.Adj
-- := fun a b ↦ ‹DecidableRel H.Adj› _ _

theorem coe_sub (H : SubTemporalGraph G) : G.IsSubtempgraph H.coe := by
  rw [SimpleTemporalGraph.IsSubtempgraph]
  intro x y n
  exact coe_adj_sub H x y n

section Spanning

/-- A SubTemporalGraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (H : SubTemporalGraph G) : Prop :=
  ∀ x : V, x ∈ H.Verts

theorem isSpanning_iff {H : SubTemporalGraph G} : H.IsSpanning ↔ H.Verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

/-- Coercion from `SubTemporalGraph G` to `SimpleTemporalGraph V`.  If `H` is a spanning
subgraph, then `H.spanningCoe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
protected def spanningCoe (H : SubTemporalGraph G) : SimpleTemporalGraph V where
  Adj := H.Adj
  symm := H.symm
  loopless := H.loopless

theorem Adj.of_spanningCoe {H : SubTemporalGraph G} {x y : H.Verts} {n : ℕ}
    (h : H.spanningCoe.Adj x y n) : G.Adj x y n :=
  H.adj_sub h

lemma spanningCoe_le (H : SubTemporalGraph G) : H.spanningCoe ≤ G := H.adj_sub

variable {H₁ : SubTemporalGraph G} {H₂ : SubTemporalGraph G}

theorem spanningCoe_inj : H₁.spanningCoe = H₂.spanningCoe ↔ H₁.Adj = H₂.Adj := by
  simp [SubTemporalGraph.spanningCoe]

end Spanning

section Props

def IsSimple (H : SubTemporalGraph G) : Prop :=
  ∀ {x y : V} {n m : ℕ}, (H.Adj x y n ∧ H.Adj x y m) → n=m

def IsClique (H : SubTemporalGraph G) : Prop := ∀ (x y : H.Verts), x ≠ y → ∃ n, H.Adj x y n

def IsProper (H : SubTemporalGraph G) : Prop :=
  ∀ (x y z : V) (n : ℕ), H.Adj x y n ∧ H.Adj x z n → y=z

-- Multigraph? One target multiple edges of different times
-- From SimpleGraph.Subgraph.IsMatching Revised
def IsStrictMatching (M : SubTemporalGraph G) : Prop :=
  -- ∀ ⦃v : V⦄, v ∈ M.Verts → ∃! w , ∃! t, M.Adj v w t
  -- Or ? First one false because exist one where exist one, and not exist one such that thing
  ∀ ⦃v : V⦄, v ∈ M.Verts → ∃! q : V × ℕ, M.Adj v q.1 q.2

-- From SimpleGraph.Subgraph.IsPerfectMatching
def IsPerfecStricttMatching (M : SubTemporalGraph G) := M.IsStrictMatching ∧ M.IsSpanning

def IsPerfectStrictMatchingOf (M : SubTemporalGraph G) (H : SubTemporalGraph G) :=
  M.IsStrictMatching ∧ M.Verts = H.Verts


instance [Finite V] {H : SubTemporalGraph G} : Finite H.Verts :=
  H.Verts.toFinite

end Props

section IncidenceSet

def IncidenceSet (H : SubTemporalGraph G) (x : V) : Set (V × ℕ) :=
  { (y, n) : V × ℕ | H.Adj x y n }

lemma finite_incidenceSet_of_finite_simple {H : SubTemporalGraph G} [h : Finite H.Verts]
    (h₁ : H.IsSimple) :
    ∀ (x : H.Verts), (H.IncidenceSet x).Finite := by
  intro x
  apply Set.Finite.of_injOn (f := fun p : V × ℕ => p.1) (t := H.Verts)
  · intro ⟨y, n⟩ hadj ; exact hadj.snd_mem
  · intro ⟨y, n⟩ hyn ⟨z, m⟩ hzm heq
    simp only at heq
    subst heq
    congr
    exact h₁ ⟨hyn, hzm⟩
  · exact h

lemma nonempty_incidenceSet_of_nontrivial_clique {H : SubTemporalGraph G} [h : Nontrivial H.Verts]
    (h₁ : H.IsClique) :
    ∀ x : H.Verts, (H.IncidenceSet x).Nonempty := by
  intro x
  have ⟨y, z, hne⟩ := h.exists_pair_ne
  by_cases heq : x=y
  · subst heq
    have ⟨n, hadj⟩ := h₁ x z hne
    have h' : ⟨z, n⟩ ∈ (H.IncidenceSet x) := hadj
    use ⟨z, n⟩
  · have ⟨n, hadj⟩ := h₁ x y heq
    have h' : ⟨y, n⟩ ∈ (H.IncidenceSet x) := hadj
    use ⟨y, n⟩

end IncidenceSet

section Order

/-- The `⊤ : SubTemporalGraph G` is `G` itself. -/
instance : Top G.SubTemporalGraph where
  top := {
    Verts := Set.univ
    Adj := G.Adj
    adj_sub := id
    symm := G.symm
    edge_vert := @fun x _ _ _ ↦ Set.mem_univ x
  }

@[simp]
theorem top_adj {x y : V} {n : ℕ} : (⊤ : SubTemporalGraph G).Adj x y n ↔ G.Adj x y n :=
  Iff.rfl

theorem top_verts : (⊤ : SubTemporalGraph G).Verts = Set.univ := rfl

theorem top_spanningCoe : (⊤ : SubTemporalGraph G).spanningCoe = G := rfl

/-- The `⊥ : SubTemporalGraph G` is the empty graph where there is no vertices. -/
instance : Bot G.SubTemporalGraph where
  bot := {
    Verts := ∅
    Adj := ⊥
    adj_sub := False.elim
    edge_vert := False.elim
    symm _ _ _ := id
  }

def IsSubgraphOf (H : SubTemporalGraph G) (H' : SubTemporalGraph G) : Prop :=
  (H.Verts ⊆ H'.Verts)
  ∧
  (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n)

instance : LE (SubTemporalGraph G) :=
  ⟨IsSubgraphOf⟩

instance : BoundedOrder (SubTemporalGraph G) where
  top := ⊤
  bot := ⊥
  le_top x := ⟨Set.subset_univ _, by intro _ _ _ h ; rw [top_adj] ; exact x.adj_sub h⟩
  bot_le _ := ⟨Set.empty_subset _, False.elim⟩

instance : LT (SubTemporalGraph G) where
  lt H H' :=
    ((H.Verts ⊂ H'.Verts) ∧ (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n))
    ∨
    ((H.Verts = H'.Verts) ∧ (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n)
      ∧ (∃ (x y : V) (n : ℕ), H'.Adj x y n ∧ ¬ H.Adj x y n))

instance : Preorder (SubTemporalGraph G) where
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

instance : PartialOrder (SubTemporalGraph G) where
  le_antisymm A B h h' := by
    ext _ _ _
    · constructor
      · intro h'' ; apply h.left ; assumption
      · intro h'' ; apply h'.left ; assumption
    · exact ⟨h.right, h'.right⟩

end Order

section Induce

/-- A SubTemporalGraph is called an *induced SubTemporalGraph* if vertices of `H` are adjacent if
they are adjacent in `G`. -/
def IsInduced (H : SubTemporalGraph G) : Prop :=
  ∀ ⦃x⦄, x ∈ H.Verts → ∀ ⦃y⦄, y ∈ H.Verts → ∀ n : ℕ, G.Adj x y n → H.Adj x y n

@[simp] lemma IsInduced.top : (⊤ : G.SubTemporalGraph).IsInduced := fun _ _ _ _ _ ↦ id

@[simps]
def induce (H : G.SubTemporalGraph) (s : Set V) : G.SubTemporalGraph where
  Verts := s
  Adj x y n := x ∈ s ∧ y ∈ s ∧ H.Adj x y n
  adj_sub h := H.adj_sub h.2.2
  edge_vert h := h.1
  symm n _ _ h := ⟨h.2.1, h.1, H.symm n h.2.2⟩

end Induce

section DeleteVerts

abbrev deleteVerts (H : SubTemporalGraph G) (s : Set V) : G.SubTemporalGraph :=
  H.induce (H.Verts \ s)

lemma deleteVerts_verts (H : SubTemporalGraph G) (s : Set V) :
    (H.deleteVerts s).Verts = H.Verts \ s :=
  rfl

theorem deleteVerts_le {H : SubTemporalGraph G} {s : Set V} : (H.deleteVerts s) ≤ H := by
  constructor <;> simp [Set.diff_subset]

theorem deleteVerts_le' (H : SubTemporalGraph G) (s : Set V) : (H.deleteVerts s) ≤ H := by
  constructor <;> simp [Set.diff_subset]


end DeleteVerts

section AddVerts

abbrev addVerts (H : SubTemporalGraph G) (s : Set V) : G.SubTemporalGraph :=
  H.induce (H.Verts ∪ s)

lemma addVerts_verts (H : SubTemporalGraph G) (s : Set V) : (H.addVerts s).Verts = H.Verts ∪ s :=
  rfl

lemma addVerts_Adj {x y : V} {n : ℕ} {H : SubTemporalGraph G} {s : Set V} :
    H.Adj x y n → (H.addVerts s).Adj x y n := by
  have hinc : H.Verts ⊆ (H.addVerts s).Verts := by simp
  intro h
  have hin := hinc <| H.edge_vert h
  have hin' := hinc <| H.edge_vert h.symm
  exact ⟨hin, hin', h⟩

lemma addVerts_le {H : SubTemporalGraph G} {s : Set V} : H ≤ (H.addVerts s) := by
  constructor
  · simp
  · intro _ _ _ h ; exact addVerts_Adj h

lemma addVerts_le' (H : SubTemporalGraph G) (s : Set V) : H ≤ (H.addVerts s) := addVerts_le

end AddVerts

section AddEdge

variable {x y : V} {n : ℕ}

def addEdge (H : SubTemporalGraph G) (h : G.Adj x y n) (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    SubTemporalGraph G where
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

variable {H : SubTemporalGraph G} {h : G.Adj x y n} {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts}

theorem addEdge_le : H ≤ addEdge H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

theorem addEdge_le' (H : SubTemporalGraph G) (h : G.Adj x y n) (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
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

def EarliestEdge (H : SubTemporalGraph G) (x y : V) (n : ℕ) : Prop :=
  H.Adj x y n ∧ ∀ (z : V) (m : ℕ), H.Adj x z m → n ≤ m

def LatestEdge (H : SubTemporalGraph G) (x y : V) (n : ℕ) : Prop :=
  H.Adj x y n ∧ ∀ (z : V) (m : ℕ), H.Adj x z m → m ≤ n

def EarliestNeighbor (H : SubTemporalGraph G) (x y : V) : Prop := ∃ n, H.EarliestEdge x y n

def LatestNeighbor (H : SubTemporalGraph G) (x y : V) : Prop := ∃ n, H.LatestEdge x y n

lemma earliestEdge_exists_of_nonempty_finite_incidenceSet {H : SubTemporalGraph G}
    (h₀ : (H.IncidenceSet x).Nonempty)
    (h₁ : (H.IncidenceSet x).Finite) :
    ∃ (y : V) (n : ℕ), H.EarliestEdge x y n := by
  haveI : Nonempty (H.IncidenceSet x) := Set.nonempty_coe_sort.mpr h₀
  have ⟨⟨⟨y, n⟩, hin⟩, hmin⟩ := h₁.exists_min (fun x ↦ x.1.2)
  use y, n
  unfold EarliestEdge
  constructor
  · trivial
  · intro z m hadj
    have hin' : ⟨z, m⟩ ∈ H.IncidenceSet x := hadj
    have hle := hmin ⟨⟨z, m⟩, hin'⟩
    simp at hle
    trivial

lemma latestEdge_exists_of_nonempty_finite_incidenceSet {H : SubTemporalGraph G}
    (h₀ : (H.IncidenceSet x).Nonempty)
    (h₁ : (H.IncidenceSet x).Finite) :
    ∃ (z : V) (m : ℕ), H.LatestEdge x z m := by
  haveI : Nonempty (H.IncidenceSet x) := Set.nonempty_coe_sort.mpr h₀
  have ⟨⟨⟨y, n⟩, hin⟩, hmax⟩ := h₁.exists_max (fun x ↦ x.1.2)
  use y, n
  unfold LatestEdge
  constructor
  · trivial
  · intro z m hadj
    have hin' : ⟨z, m⟩ ∈ H.IncidenceSet x := hadj
    have hle := hmax ⟨⟨z, m⟩, hin'⟩
    simp at hle
    trivial

lemma subgraph_earliestEdge_of_graph_earliestEdge {H : SubTemporalGraph G}
    (h : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.EarliestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert h₁.symm⟩ n := by
  constructor
  · exact h₁
  · rw [SimpleTemporalGraph.EarliestEdge] at h
    rcases h with ⟨hαβ, hmin⟩
    intro z m hadj
    cases z with
    | mk z hz => exact hmin z m <| H.adj_sub hadj

lemma subgraph_latestEdge_of_graph_latestEdge {H : SubTemporalGraph G}
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
abbrev Iso (G' : SubTemporalGraph G) (H' : SubTemporalGraph H)
:= G'.coe ≃tg H'.coe

@[inherit_doc] infixl:50 " ≃stg " => Iso

end Iso

end Maps

section NeighborSet

def NeighborSet (H : SubTemporalGraph G) (x : V) := {y | ∃ n, H.Adj x y n}

theorem mem_neighborSet (H : SubTemporalGraph G) (x y : V) :
    y ∈ H.NeighborSet x ↔ ∃ n, H.Adj x y n :=
  Iff.rfl

theorem neighborSet_top (v : V) : (⊤ : G.SubTemporalGraph).NeighborSet v = G.NeighborSet v := rfl

theorem neighborSet_subset_verts (H : SubTemporalGraph G) (x : V) : H.NeighborSet x ⊆ H.Verts := by
  intro _ h
  rw [mem_neighborSet] at h
  let ⟨_, h⟩ := h
  exact H.edge_vert <| H.adj_symm h

end NeighborSet

end SubTemporalGraph

namespace NonemptyTemporalWalk

variable {V : Type u} {G : SimpleTemporalGraph V} {H : SubTemporalGraph G}

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
protected def lift_subtempgraph_walk' {H' : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ}
    (h : H ≤ H') :
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

variable {V : Type u} {G : SimpleTemporalGraph V} {H : SubTemporalGraph G}

@[coe]
protected def lift_subtempgraph_walk {x y : H.Verts} {n m : ℕ} :
    H.coe.TemporalWalk x n y m → G.TemporalWalk ↑x n ↑y m
  | Empty => Empty
  | Nonempty p => Nonempty ↑p

instance {x y : H.Verts} {n m : ℕ} : Coe (H.coe.TemporalWalk x n y m)
    (G.TemporalWalk ↑x n ↑y m) where
  coe := TemporalWalk.lift_subtempgraph_walk

@[coe]
protected def lift_subtempgraph_walk' {H' : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ}
    (h : H ≤ H') :
    H.coe.TemporalWalk x n y m → H'.coe.TemporalWalk
      ⟨x, Set.mem_of_subset_of_mem h.left x.prop⟩ n
      ⟨y, Set.mem_of_subset_of_mem h.left y.prop⟩ m
  | Empty => Empty
  | Nonempty p => Nonempty <| p.lift_subtempgraph_walk' h

end TemporalWalk

section SubgraphProps

variable {V : Type u} {G : SimpleTemporalGraph V}

@[simps]
def toSubgraph (H : SimpleTemporalGraph V) (h : H ≤ G) : G.SubTemporalGraph where
  Verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  symm _ := H.symm _

theorem toSubgraph.isSpanning (H : SimpleTemporalGraph V) (h : H ≤ G) :
    (toSubgraph H h).IsSpanning :=
  Set.mem_univ

def toSubgraphTop : G.SubTemporalGraph := ⊤

-- If edges are bigger than `G` then they are ignored
def fromEdgeSet (G : SimpleTemporalGraph V) (s : Set (V × V × ℕ)) : SubTemporalGraph G where
  Verts := {x | ∃ a ∈ s, x = a.1 ∨ x = a.2.1}
  Adj x y n := ∃ a ∈ s, ((x = a.1 ∧ y = a.2.1) ∨ (x = a.2.1 ∧ y = a.1)) ∧ n = a.2.2 ∧ G.Adj x y n

  adj_sub h := by
    have ⟨a, h⟩ := h
    exact h.2.2.2

  edge_vert h := by
    obtain ⟨a, h⟩ := h
    simp only [Prod.exists, exists_and_right, Set.mem_setOf_eq]
    use a.1, a.2.1
    constructor
    · use a.2.2 ; exact h.1
    · apply h.2.1.elim
    <;> intro h'
      · exact Or.inl h'.1
      · exact Or.inr h'.1

  symm _ _ _ h := by
    simp_all only [Prod.exists, ↓existsAndEq, true_and]
    have ⟨x, y, h⟩ := h
    use x, y
    constructor
    · exact h.1
    · constructor
      · apply h.2.1.elim
        <;> intro h'
        · exact Or.inr h'.symm
        · exact Or.inl h'.symm
      · exact h.2.2.symm

end SubgraphProps

end SimpleTemporalGraph
