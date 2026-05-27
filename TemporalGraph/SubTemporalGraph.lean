/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.TemporalWalk

universe u

namespace LooplessTemporalGraph


@[ext]
structure SubTemporalGraph {V : Type u} (G : LooplessTemporalGraph V) where
  Verts : Set V
  Adj : V → V → ℕ → Prop

  adj_sub : ∀ {x y : V} {n : ℕ}, Adj x y n → G.Adj x y n
  edge_vert : ∀ {x y : V} {n : ℕ}, Adj x y n → x ∈ Verts
  symm : ∀ n, Symmetric (fun x y => Adj x y n)

namespace SubTemporalGraph

variable {V : Type u} {G : LooplessTemporalGraph V}

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

protected theorem Adj.ne {H : SubTemporalGraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    x ≠ y :=
  h.adj_sub.ne

protected theorem Adj.ne' {H : SubTemporalGraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    y ≠ x :=
  h.adj_sub.ne'

protected theorem Adj.fst_mem {H : G.SubTemporalGraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    u ∈ H.Verts :=
  H.edge_vert h

protected theorem Adj.snd_mem {H : G.SubTemporalGraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    y ∈ H.Verts :=
  h.symm.fst_mem

/-- Coercion from `H : SubTemporalGraph G` to a `LooplessTemporalGraph H.Verts`. -/
@[simps, coe]
protected def coe (H : SubTemporalGraph G) : LooplessTemporalGraph H.Verts where
  Adj x y n := H.Adj x y n
  symm n _ _ h := H.symm n h
  loopless _ := ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩

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

theorem coe_sub (H : SubTemporalGraph G) : G.IsSubtempgraph H.coe := by
  rw [LooplessTemporalGraph.IsSubtempgraph]
  intro x y n
  exact coe_adj_sub H x y n

section Spanning

/-- A SubTemporalGraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (H : SubTemporalGraph G) : Prop :=
  ∀ x : V, x ∈ H.Verts

theorem isSpanning_iff {H : SubTemporalGraph G} : H.IsSpanning ↔ H.Verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

/-- Coercion from `SubTemporalGraph G` to `LooplessTemporalGraph V`.  If `H` is a spanning
subgraph, then `H.spanningCoe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
protected def spanningCoe (H : SubTemporalGraph G) : LooplessTemporalGraph V where
  Adj := H.Adj
  symm := H.symm
  loopless := H.loopless

theorem Adj.of_spanningCoe {H : SubTemporalGraph G} {x y : H.Verts} {n : ℕ}
    (h : H.spanningCoe.Adj x y n) : G.Adj x y n :=
  H.adj_sub h

lemma spanningCoe_le (H : SubTemporalGraph G) : H.spanningCoe ≤ G := H.adj_sub

theorem spanningCoe_adj_iff {H : SubTemporalGraph G} {x y : V} {n : ℕ} :
    H.spanningCoe.Adj x y n ↔ H.Adj x y n := by
  simp only [spanningCoe_Adj]

variable {H₁ : SubTemporalGraph G} {H₂ : SubTemporalGraph G}

theorem spanningCoe_inj : H₁.spanningCoe = H₂.spanningCoe ↔ H₁.Adj = H₂.Adj := by
  simp [SubTemporalGraph.spanningCoe]

end Spanning

section Props

def IsSimple (H : SubTemporalGraph G) : Prop :=
  ∀ {x y : V} {n m : ℕ}, (H.Adj x y n ∧ H.Adj x y m) → n=m

@[simp]
lemma isSimple_iff_coe {H : SubTemporalGraph G} : H.IsSimple ↔ H.coe.IsSimple := by
  unfold IsSimple LooplessTemporalGraph.IsSimple
  constructor
  · intro h _ _ _ _ h'
    exact h h'
  · intro h x y _ _ h'
    exact h ⟨x, h'.1.fst_mem⟩ ⟨y, h'.1.snd_mem⟩ _ _ h'

def IsClique (H : SubTemporalGraph G) : Prop := ∀ (x y : H.Verts), x ≠ y → ∃ n, H.Adj x y n

@[simp]
lemma isClique_iff_coe {H : SubTemporalGraph G} : H.IsClique ↔ H.coe.IsComplete := by
  simp only [IsClique, ne_eq, Subtype.forall, Subtype.mk.injEq, IsComplete, coe_Adj]

def IsProper (H : SubTemporalGraph G) : Prop :=
  ∀ {x y z : V} {n : ℕ}, H.Adj x y n ∧ H.Adj x z n → y=z

@[simp]
lemma isProper_iff_coe {H : SubTemporalGraph G} : H.IsProper ↔ H.coe.IsProper := by
  unfold IsProper LooplessTemporalGraph.IsProper
  constructor
  · intro h _ _ _ _ h'
    have := h h'
    rw [Subtype.val_inj] at this
    assumption
  · intro h x y z n h'
    have := h ⟨x, h'.1.fst_mem⟩ ⟨y, h'.1.snd_mem⟩ ⟨z, h'.2.snd_mem⟩ n h'
    rw [←Subtype.val_inj] at this
    assumption

def IsHappy (H : SubTemporalGraph G) : Prop :=
  H.IsSimple ∧ H.IsProper

@[simp]
lemma isHappy_iff_coe {H : SubTemporalGraph G} : H.IsHappy ↔ H.coe.IsHappy := by
  unfold IsHappy LooplessTemporalGraph.IsHappy
  simp only [isSimple_iff_coe, isProper_iff_coe]

instance [Finite V] {H : SubTemporalGraph G} : Finite H.Verts :=
  H.Verts.toFinite


-- From SimpleGraph.Subgraph.IsMatching Revised
def IsMatching (M : SubTemporalGraph G) : Prop :=
  ∀ ⦃v : V⦄, v ∈ M.Verts → ∃! q : V × ℕ, M.Adj v q.1 q.2

-- From SimpleGraph.Subgraph.IsPerfectMatching
def IsPerfectMatching (M : SubTemporalGraph G) := M.IsMatching ∧ M.IsSpanning

def IsPerfectMatchingOf (M : SubTemporalGraph G) (H : SubTemporalGraph G) :=
  M.IsMatching ∧ M.Verts = H.Verts

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

instance {H : SubTemporalGraph G} [Finite H.Verts] {h₀ : H.IsSimple} {x : H.Verts} :
    Finite (H.IncidenceSet x) :=
  finite_incidenceSet_of_finite_simple h₀ x

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

theorem top_isSpanning : (⊤ : SubTemporalGraph G).IsSpanning := by simp [IsSpanning, top_verts]

/-- The `⊥ : SubTemporalGraph G` is the empty graph where there is no vertices. -/
instance : Bot G.SubTemporalGraph where
  bot := {
    Verts := ∅
    Adj := ⊥
    adj_sub := False.elim
    edge_vert := False.elim
    symm _ _ _ := id
  }

@[simp]
def IsSubTemporalGraphOf (H : SubTemporalGraph G) (H' : SubTemporalGraph G) : Prop :=
  (H.Verts ⊆ H'.Verts)
  ∧
  (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n)

instance : LE (SubTemporalGraph G) :=
  ⟨IsSubTemporalGraphOf⟩

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
          · have h := h.right ; dsimp [LE.le, IsSubTemporalGraphOf] at h ; push_neg at h
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
  ∀ ⦃x⦄, x ∈ H.Verts → ∀ ⦃y⦄, y ∈ H.Verts → ∀ ⦃n : ℕ⦄, G.Adj x y n → H.Adj x y n

@[simp] lemma IsInduced.top : (⊤ : G.SubTemporalGraph).IsInduced := fun _ _ _ _ _ ↦ id

/-- Create the induced subgraph on `G` from another subgraph on `G`, it might not be induced to `G`.
-/
@[simps]
def induce (H : G.SubTemporalGraph) (s : Set V) : G.SubTemporalGraph where
  Verts := s
  Adj x y n := x ∈ s ∧ y ∈ s ∧ H.Adj x y n
  adj_sub h := H.adj_sub h.2.2
  edge_vert h := h.1
  symm n _ _ h := ⟨h.2.1, h.1, H.symm n h.2.2⟩

lemma isInduced_of_top_induce {s : Set V} : (induce (⊤ : SubTemporalGraph G) s).IsInduced := by
  intro x hx y hy n h
  refine ⟨hx, hy, h⟩

end Induce

section DeleteVerts

abbrev deleteVerts (H : SubTemporalGraph G) (s : Set V) : G.SubTemporalGraph :=
  H.induce (H.Verts \ s)

lemma deleteVerts_verts (H : SubTemporalGraph G) (s : Set V) :
    (H.deleteVerts s).Verts = H.Verts \ s :=
  rfl

@[simp]
theorem deleteVerts_le {H : SubTemporalGraph G} {s : Set V} : (H.deleteVerts s) ≤ H := by
  constructor <;> simp [Set.diff_subset]

theorem deleteVerts_le' (H : SubTemporalGraph G) (s : Set V) : (H.deleteVerts s) ≤ H := by
  constructor <;> simp [Set.diff_subset]


end DeleteVerts

section AddVerts

abbrev addVerts (H : SubTemporalGraph G) (s : Set V) : G.SubTemporalGraph :=
  H.induce (H.Verts ∪ s)

@[simp]
lemma addVerts_verts (H : SubTemporalGraph G) (s : Set V) : (H.addVerts s).Verts = H.Verts ∪ s :=
  rfl

lemma addVerts_Adj {x y : V} {n : ℕ} {H : SubTemporalGraph G} {s : Set V} :
    H.Adj x y n → (H.addVerts s).Adj x y n := by
  have hinc : H.Verts ⊆ (H.addVerts s).Verts := by simp
  intro h
  have hin := hinc <| H.edge_vert h
  have hin' := hinc <| H.edge_vert h.symm
  exact ⟨hin, hin', h⟩

@[simp]
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

@[simp]
theorem addEdge_le : H ≤ addEdge H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

theorem addEdge_le' (H : SubTemporalGraph G) (h : G.Adj x y n) (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    H ≤ addEdge H h h₁ :=
  addEdge_le

@[simp]
theorem addEdge_edge : (addEdge H h h₁).Adj x y n := by
  right
  left
  exact ⟨rfl, rfl, rfl⟩

@[simp]
theorem addEdge_verts : (addEdge H h h₁).Verts = H.Verts := rfl

end AddEdge

section EdgeProps

variable {x y : V} {n : ℕ}

def EarliestEdge (H : SubTemporalGraph G) (x y : V) (n : ℕ) : Prop :=
  H.Adj x y n ∧ ∀ (z : V) (m : ℕ), H.Adj x z m → n ≤ m

lemma top_earliestEdge :
    (⊤ : SubTemporalGraph G).EarliestEdge x y n ↔ G.EarliestEdge x y n := by
  simp [EarliestEdge, LooplessTemporalGraph.EarliestEdge, top_adj]

def LatestEdge (H : SubTemporalGraph G) (x y : V) (n : ℕ) : Prop :=
  H.Adj x y n ∧ ∀ (z : V) (m : ℕ), H.Adj x z m → m ≤ n

lemma top_latestEdge :
    (⊤ : SubTemporalGraph G).LatestEdge x y n ↔ G.LatestEdge x y n := by
  simp [LatestEdge, LooplessTemporalGraph.LatestEdge, top_adj]

@[simp]
lemma earliestEdge_lt_of_proper {H : SubTemporalGraph G} {z : V} {m : ℕ}
    (h₀ : H.IsProper)
    (h₁ : H.EarliestEdge x y n)
    (h₂ : H.Adj x z m)
    (h₄ : y ≠ z) :
    n < m := by
  have hle := h₁.right _ _ h₂
  apply hle.lt_of_ne
  by_contra h
  rw [←h] at h₂
  absurd (h₀ ⟨h₁.left, h₂⟩)
  exact h₄

def EarliestNeighbor (H : SubTemporalGraph G) (x y : V) : Prop := ∃ n, H.EarliestEdge x y n

lemma top_earliestNeighbor :
    (⊤ : SubTemporalGraph G).EarliestNeighbor x y ↔ G.EarliestNeighbor x y := by
  simp [EarliestNeighbor, LooplessTemporalGraph.EarliestNeighbor, top_earliestEdge]

def LatestNeighbor (H : SubTemporalGraph G) (x y : V) : Prop := ∃ n, H.LatestEdge x y n

lemma top_latestNeighbor :
    (⊤ : SubTemporalGraph G).LatestNeighbor x y ↔ G.LatestNeighbor x y := by
  simp [LatestNeighbor, LooplessTemporalGraph.LatestNeighbor, top_latestEdge]

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

@[simp]
lemma coe_earliestEdge {H : SubTemporalGraph G} {x y : H.Verts} {n : ℕ}
    (h₀ : H.EarliestEdge x y n) :
    H.coe.EarliestEdge x y n := by
  constructor
  · simp [h₀.left]
  · intro _ _ h
    exact h₀.right _ _ h

@[simp]
lemma coe_latestEdge {H : SubTemporalGraph G} {x y : H.Verts} {n : ℕ}
    (h₀ : H.LatestEdge x y n) :
    H.coe.LatestEdge x y n := by
  constructor
  · simp [h₀.left]
  · intro _ _ h
    exact h₀.right _ _ h

end EdgeProps

section NeighborHoodSet

def NeighborhoodSet (H : SubTemporalGraph G) (x : H.Verts) := {y | ∃ n, H.Adj x y n}

theorem mem_neighborhoodSet (H : SubTemporalGraph G) (x : H.Verts) (y : V) :
    y ∈ H.NeighborhoodSet x ↔ ∃ n, H.Adj x y n :=
  Iff.rfl

theorem neighborhoodSet_top (x : (⊤ : G.SubTemporalGraph).Verts) :
    (⊤ : G.SubTemporalGraph).NeighborhoodSet x = G.NeighborhoodSet x := rfl

theorem neighborSet_subset_verts (H : SubTemporalGraph G) (x : H.Verts) :
    H.NeighborhoodSet x ⊆ H.Verts := by
  intro _ h
  rw [mem_neighborhoodSet] at h
  let ⟨_, h⟩ := h
  exact H.edge_vert <| H.adj_symm h

@[simp]
lemma neighborhoodSet_iff_coe {H : SubTemporalGraph G} {x : H.Verts} :
    H.NeighborhoodSet x = H.coe.NeighborhoodSet x := by
  unfold NeighborhoodSet LooplessTemporalGraph.NeighborhoodSet
  ext y
  constructor
  · intro ⟨_, p⟩
    simp only [coe_Adj, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left,
      exists_prop, exists_eq_right_right]
    exact ⟨⟨_, p⟩, p.snd_mem⟩
  · intro h
    simp only [coe_Adj, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left,
      exists_prop, exists_eq_right_right] at h ⊢
    exact h.1

end NeighborHoodSet

section EdgeSet

def EdgeSet (H : SubTemporalGraph G) : Set ((Sym2 V) × ℕ) :=
  {(p, n) | ∃ x y : p, H.Adj x y n}

@[simp]
theorem mem_edgeSet (H : SubTemporalGraph G) {x y : V} {n : ℕ} :
    (s(x,y), n) ∈ H.EdgeSet ↔ H.Adj x y n := by
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

@[simp]
lemma edgeSet_le {H : SubTemporalGraph G} {H' : SubTemporalGraph G} (h₀ : H ≤ H') :
    H.EdgeSet ⊆ H'.EdgeSet := by
  intro _ ⟨_, _, h⟩
  exact ⟨_, _, h₀.right h⟩

@[simp]
lemma addEdge_edgeSet (H : SubTemporalGraph G) {x y : V} {n : ℕ}
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts} :
    (H.addEdge h₀ h₁).EdgeSet = insert ⟨s(x,y), n⟩ H.EdgeSet := by
  unfold addEdge EdgeSet
  simp only [Subtype.exists, exists_prop]
  ext a
  apply Iff.intro
  <;> intro h
  · have ⟨b, hb, c, hc, hadj⟩ := h
    apply Or.elim3 hadj
    <;> intro h'
    · apply Or.inr
      use b, hb, c, hc
    · apply Or.inl ; apply Prod.ext
      · rw [h'.1.symm, h'.2.1.symm] at h₀ ⊢
        exact a.1.mem_and_mem_iff h₀.ne |>.mp ⟨hb, hc⟩
      · simp only [h']
    · apply Or.inl ; apply Prod.ext
      · rw [h'.1.symm, h'.2.1.symm] at h₀ ⊢
        exact a.1.mem_and_mem_iff h₀.ne |>.mp ⟨hc, hb⟩
      · simp only [h']
  · apply Or.elim h
    <;> intro h
    · have hx : x ∈ a.1 := by simp only [h, Sym2.mem_iff, true_or]
      have hy : y ∈ a.1 := by simp only [h, Sym2.mem_iff, or_true]
      use x, hx, y, hy
      apply Or.inr ; apply Or.inl
      simp only [h, and_self]
    · have ⟨b, hb, c, hc, hadj⟩ := h
      use b, hb, c, hc
      exact Or.inl hadj

lemma addEdge_edgeSet' (H : SubTemporalGraph G) {x y : V} {n : ℕ}
    (h₀ : G.Adj x y n)
    (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    (H.addEdge h₀ h₁).EdgeSet = insert ⟨s(x,y), n⟩ H.EdgeSet :=
  H.addEdge_edgeSet

instance {H : SubTemporalGraph G} [h : Finite H.EdgeSet] {x y : V} {n : ℕ}
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts} :
    Finite (H.addEdge h₀ h₁).EdgeSet := by
  conv =>
    rhs ; rw [addEdge_edgeSet, ←Set.union_singleton]
  apply Set.Finite.union
  · exact h
  · simp only [Set.finite_singleton]

@[simp]
lemma addVerts_edgeSet {H : SubTemporalGraph G} {s : Set V} :
    (H.addVerts s).EdgeSet = H.EdgeSet := by
  simp only [EdgeSet, addVerts, induce, Set.mem_union, exists_and_left, Subtype.exists, exists_prop]
  ext a
  apply Iff.intro
  <;> intro h
  · have ⟨x, _, hx', y, _, hy', _⟩ := h
    use x, hx', y, hy'
  · have ⟨x, hx, y, hy, hadj⟩ := h
    use x, Or.inl hadj.fst_mem, hx, y, Or.inl hadj.snd_mem

lemma addVerts_edgeSet' {H : SubTemporalGraph G} (s : Set V) :
    (H.addVerts s).EdgeSet = H.EdgeSet := addVerts_edgeSet

instance {H : SubTemporalGraph G} {s : Set V} [h₀ : Finite H.EdgeSet] [Finite s] :
    Finite (H.addVerts s).EdgeSet := by
  simp only [addVerts_edgeSet, h₀]

lemma spanningCoe_edgeSet_eq {H : SubTemporalGraph G} :
    H.EdgeSet = H.spanningCoe.EdgeSet := by
  simp [EdgeSet, LooplessTemporalGraph.EdgeSet]

def FootprintEdgeSet (H : SubTemporalGraph G) : Set (Sym2 V) :=
  {p | ∃ n : ℕ, ∃ x y : p, H.Adj x y n}

theorem FootprintEdgeSet_eq {H : SubTemporalGraph G} :
    H.spanningCoe.Footprint.edgeSet = H.FootprintEdgeSet := by
  simp only [Footprint, spanningCoe_Adj, FootprintEdgeSet, Subtype.exists, exists_prop]
  ext a
  apply Iff.intro
  · intro ha
    obtain ⟨x, y⟩ := a
    simp only [SimpleGraph.mem_edgeSet, Set.mem_setOf_eq, Sym2.mem_iff, exists_eq_or_imp,
      ↓existsAndEq, true_and, SubTemporalGraph.irrefl, false_or, or_false] at ha ⊢
    obtain ⟨n, hadj⟩ := ha
    use n
    apply Or.inl hadj
  · intro ha
    obtain ⟨x, y⟩ := a
    simp only [Set.mem_setOf_eq, Sym2.mem_iff, exists_eq_or_imp, ↓existsAndEq, true_and,
      SubTemporalGraph.irrefl, false_or, or_false, SimpleGraph.mem_edgeSet] at ha ⊢
    obtain ⟨n, hadj⟩ := ha
    use n
    apply hadj.elim
    · intro _ ; trivial
    · intro h ; exact h.symm

def EdgeSetToFootprintEdgeSet (H : SubTemporalGraph G) : H.EdgeSet → H.FootprintEdgeSet :=
  fun x ↦ ⟨x.val.fst, ⟨x.val.snd, by
    have ⟨a, b, hadj⟩ := x.2
    use a, b
  ⟩⟩

lemma edgeSetToFootprintEdgeSet_surjective (H : SubTemporalGraph G) :
    Function.Surjective H.EdgeSetToFootprintEdgeSet := by
  intro x
  simp only [Subtype.exists, Prod.exists]
  have ⟨n, a, b ,hadj⟩ := x.prop
  use x.1, n, ⟨a, b, hadj⟩
  simp only [EdgeSetToFootprintEdgeSet, Subtype.coe_eta]

lemma edgeSetToFootprintEdgeSet_injective (H : SubTemporalGraph G) (h₀ : H.IsSimple) :
    Function.Injective H.EdgeSetToFootprintEdgeSet := by
  intro x y h
  have ⟨a, b, hadj⟩ := x.prop
  have ⟨a', b', hadj'⟩ := y.prop
  simp only [EdgeSetToFootprintEdgeSet, Subtype.mk.injEq] at h
  ext
  · apply Sym2.ext_iff.mp h
  · refine h₀ ⟨hadj, ?_⟩
    have hxs := x.1.1.mem_and_mem_iff hadj.adj_sub.ne |>.mp ⟨a.prop, b.prop⟩
    have hys := y.1.1.mem_and_mem_iff hadj'.adj_sub.ne |>.mp ⟨a'.prop, b'.prop⟩
    rw [hxs, hys] at h
    rcases Sym2.eq_iff.mp h with heq | heq
    · rw [heq.1.symm, heq.2.symm] at hadj'
      exact hadj'
    · rw [heq.1.symm, heq.2.symm] at hadj'
      exact hadj'.symm

lemma edgeSetToFootprintEdgeSet_bijective (H : SubTemporalGraph G) (h₀ : H.IsSimple) :
    Function.Bijective H.EdgeSetToFootprintEdgeSet :=
  ⟨H.edgeSetToFootprintEdgeSet_injective h₀, H.edgeSetToFootprintEdgeSet_surjective⟩

end EdgeSet

section Size

def size (H : SubTemporalGraph G) [Fintype H.EdgeSet] := Fintype.card H.EdgeSet

def order (H : SubTemporalGraph G) [Fintype H.Verts] := Fintype.card H.Verts

lemma size_of_simple (H : SubTemporalGraph G)
    [Fintype H.EdgeSet]
    [Fintype H.FootprintEdgeSet]
    (h₀ : H.IsSimple) :
    H.size = Fintype.card H.FootprintEdgeSet := by
  apply Fintype.card_of_bijective (f := H.EdgeSetToFootprintEdgeSet)
  exact H.edgeSetToFootprintEdgeSet_bijective h₀

lemma size_of_spanningCoe (H : SubTemporalGraph G)
    [Fintype H.EdgeSet]
    [Fintype H.spanningCoe.EdgeSet] :
    H.size = H.spanningCoe.size := by
  unfold size LooplessTemporalGraph.size
  simp only [spanningCoe_edgeSet_eq]

theorem addEdge_size (H : SubTemporalGraph G) {x y : V} {n : ℕ}
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts}
    {h₂ : ¬H.Adj x y n}
    [Fintype H.EdgeSet] :
    (H.addEdge h₀ h₁).size = H.size + 1 := by
  simp only [size, addEdge_edgeSet, mem_edgeSet, h₂, not_false_eq_true, Set.card_insert]

@[simp]
theorem addEdge_size_le (H : SubTemporalGraph G) {x y : V} {n : ℕ}
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts}
    [Fintype H.EdgeSet] :
    (H.addEdge h₀ h₁).size ≤ H.size + 1 := by
  unfold size
  have h : (H.addEdge h₀ h₁).EdgeSet = H.EdgeSet ∪ {(s(x,y), n)} := by simp only [addEdge_edgeSet,
    Set.union_singleton]
  have h' := Set.card_union_le H.EdgeSet {(s(x,y), n)}
  simp only [h, Nat.card_eq_fintype_card, Set.card_singleton] at h' ⊢
  assumption

theorem addEdge_size_le' (H : SubTemporalGraph G) {x y : V} {n : ℕ}
    (h₀ : G.Adj x y n)
    (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts)
    [Fintype H.EdgeSet] :
    Fintype.card (H.addEdge h₀ h₁).EdgeSet ≤ Fintype.card H.EdgeSet + 1 := by
  exact H.addEdge_size_le

@[simp]
theorem addVerts_size {H : SubTemporalGraph G} {s : Set V}
    [Fintype H.EdgeSet]
    [Fintype (H.addVerts s).EdgeSet] :
    Fintype.card (H.addVerts s).EdgeSet = Fintype.card H.EdgeSet := by
  simp only [addVerts_edgeSet]

end Size

end SubTemporalGraph

namespace NonemptyTemporalWalk

variable {V : Type u} {G : LooplessTemporalGraph V}

@[coe]
protected def lift_walk {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    H.coe.NonemptyTemporalWalk x n y m → G.NonemptyTemporalWalk ↑x n ↑y m
  | Single h => Single (H.adj_sub h)
  | Step p h h' =>
    Step (p.lift_walk)
      (H.adj_sub h)
      h'

instance {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    Coe (H.coe.NonemptyTemporalWalk x n y m) (G.NonemptyTemporalWalk ↑x n ↑y m) where
  coe := NonemptyTemporalWalk.lift_walk

@[coe]
protected def lift_subTemporalTraph_walk {H : SubTemporalGraph G} {H' : SubTemporalGraph G}
    {x y : H.Verts}
    {n m : ℕ}
    (h : H ≤ H') :
    H.coe.NonemptyTemporalWalk x n y m → H'.coe.NonemptyTemporalWalk
      ⟨x, Set.mem_of_subset_of_mem h.left x.prop⟩ n
      ⟨y, Set.mem_of_subset_of_mem h.left y.prop⟩ m
  | Single h' => Single (h.right h')
  | Step p h' hle =>
    Step (NonemptyTemporalWalk.lift_subTemporalTraph_walk h p)
      (h.right h').coe
      hle

@[coe]
protected def lift_spanningCoe_walk {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    H.spanningCoe.NonemptyTemporalWalk x n y m → H.coe.NonemptyTemporalWalk x n y m
  | Single h => @Single H.Verts H.coe x y n (SubTemporalGraph.spanningCoe_adj_iff.mp h)
  | @Step _ _ _ y' _ _ m' _ p' h' hle' =>
      @Step H.Verts H.coe x ⟨y', h'.fst_mem⟩ y n m' m
        (p'.lift_spanningCoe_walk)
        (SubTemporalGraph.spanningCoe_adj_iff.mp h') hle'

instance {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    Coe (H.spanningCoe.NonemptyTemporalWalk x n y m) (H.coe.NonemptyTemporalWalk x n y m) where
  coe p := p.lift_spanningCoe_walk

end NonemptyTemporalWalk

namespace TemporalWalk

variable {V : Type u} {G : LooplessTemporalGraph V} {H : SubTemporalGraph G}

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
  | Nonempty p => Nonempty <| p.lift_subTemporalTraph_walk h

end TemporalWalk

section SubgraphProps

variable {V : Type u} {G : LooplessTemporalGraph V}

@[simps]
def toSubTemporalGraph (H : LooplessTemporalGraph V) (h : H ≤ G) : G.SubTemporalGraph where
  Verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  symm _ := H.symm _

theorem toSubgraph.isSpanning (H : LooplessTemporalGraph V) (h : H ≤ G) :
    (toSubTemporalGraph H h).IsSpanning :=
  Set.mem_univ

def toSubgraphTop : G.SubTemporalGraph := ⊤

/-- Create a `SubTemporalGraph G` from a set of edges, the edges not in `G.EdgeSet` are ignored. -/
@[simps]
def fromEdgeSet (G : LooplessTemporalGraph V) (s : Set ((Sym2 V) × ℕ)) : SubTemporalGraph G where
  Verts := {x | ∃ (p : s) , x ∈ p.1.1 }
  Adj x y n := ∃ (a : s), x ∈ a.1.1 ∧ y ∈ a.1.1 ∧ n = a.1.2 ∧ G.Adj x y n

  adj_sub h := by
    have ⟨_, h⟩ := h
    exact h.2.2.2

  edge_vert h := by
    obtain ⟨a, h⟩ := h
    use a
    exact h.1

  symm _ _ _ h := by
    simp only [Subtype.exists, exists_and_left, exists_prop, Prod.exists, ↓existsAndEq,
      true_and] at ⊢ h
    obtain ⟨a, h⟩ := h
    use a
    simp only [h, h.2.2.2.symm, and_self]

@[simp]
theorem fromEdgeSet_eq {G : LooplessTemporalGraph V} {s : Set ((Sym2 V) × ℕ)} (h₀ : s ⊆ G.EdgeSet) :
    (G.fromEdgeSet s).EdgeSet = s := by
  simp only [SubTemporalGraph.EdgeSet, fromEdgeSet, Subtype.exists, exists_prop, Prod.exists,
    exists_and_right, ↓existsAndEq, true_and]
  ext a
  constructor
  · simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro x hx y hy b hb hbx hby hG
    have heq : a.1=b := by
      apply a.1.eq_of_ne_mem hG.ne
      <;> trivial
    rwa [←heq] at hb
  · intro ha
    simp only [Set.mem_setOf_eq]
    obtain ⟨⟨x, y⟩, n⟩ := a
    use x
    simp only [Sym2.mem_iff, true_or, exists_eq_or_imp, LooplessTemporalGraph.irrefl, and_false,
      exists_false, ↓existsAndEq, true_and, false_or]
    use s(x,y)
    simp only [Sym2.mem_iff, true_or, or_true, ha, true_and]
    rw [←mem_edgeSet]
    have : (s(x,y), n) ∈ s := by simp only [ha]
    apply Set.mem_of_subset_of_mem h₀ this


end SubgraphProps

end LooplessTemporalGraph
