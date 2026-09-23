/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.TemporalWalk

universe u

namespace TemporalGraph


@[ext]
structure SubTemporalGraph {V : Type u} (G : TemporalGraph V) extends TemporalGraph V where
  Verts : Set V

  adj_sub : ∀ {x y : V} {n : ℕ}, Adj x y n → G.Adj x y n
  edge_vert : ∀ {x y : V} {n : ℕ}, Adj x y n → x ∈ Verts
  edge_vert' : ∀ {x y : V} {n : ℕ}, Adj x y n → y ∈ Verts

namespace SubTemporalGraph

variable {V : Type u} {G : TemporalGraph V}

-- `IsSymm` is no longer redefined here: `SubTemporalGraph` now `extends TemporalGraph V`, so
-- `H.IsSymm` resolves through generalized field notation to
-- `TemporalGraph.IsSymm H.toTemporalGraph`.

/-- A subgraph of a loopless graph is loopless: an instance, so that `[G.IsLoopless]` alone
suffices at every use site, however deeply the subgraph is built up. -/
instance loopless (H : SubTemporalGraph G) [G.IsLoopless] : H.IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩⟩

@[simp]
protected theorem irrefl {H : SubTemporalGraph G} [G.IsLoopless] {x : V} {n : ℕ} :
    ¬H.Adj x x n :=
  TemporalGraph.irrefl

theorem adj_comm (H : SubTemporalGraph G) [hs : H.IsSymm] (x y : V) (n : ℕ) :
    H.Adj x y n ↔ H.Adj y x n :=
  ⟨fun h ↦ hs.symm n h, fun h ↦ hs.symm n h⟩

-- No `@[symm]`: `TemporalGraph.adj_symm` already carries the attribute and applies here, since
-- `H.Adj` *is* `H.toTemporalGraph.Adj`.
theorem adj_symm (H : SubTemporalGraph G) [hs : H.IsSymm] {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.Adj y x n :=
  hs.symm n h

protected theorem Adj.symm {H : SubTemporalGraph G} [hs : H.IsSymm] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    H.Adj y x n :=
  hs.symm n h

protected theorem Adj.adj_sub {H : G.SubTemporalGraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    G.Adj u v t :=
  H.adj_sub h

protected theorem Adj.ne {H : SubTemporalGraph G} [G.IsLoopless] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    x ≠ y :=
  (H.adj_sub h).ne

protected theorem Adj.ne' {H : SubTemporalGraph G} [G.IsLoopless] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    y ≠ x :=
  (H.adj_sub h).ne'

protected theorem Adj.fst_mem {H : G.SubTemporalGraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    u ∈ H.Verts :=
  H.edge_vert h

protected theorem Adj.snd_mem {H : G.SubTemporalGraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    y ∈ H.Verts :=
  H.edge_vert' h

/-- Coercion from `H : SubTemporalGraph G` to a `TemporalGraph H.Verts`. -/
@[simps, coe]
protected def coe (H : SubTemporalGraph G) : TemporalGraph H.Verts where
  Adj x y n := H.Adj x y n

instance coe_isSymm (H : SubTemporalGraph G) [hs : H.IsSymm] : H.coe.IsSymm :=
  ⟨fun n _ _ h ↦ hs.symm n h⟩

instance coe_isLoopless (H : SubTemporalGraph G) [G.IsLoopless] : H.coe.IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩⟩

@[simp]
theorem Adj.adj_sub' (H : SubTemporalGraph G) (x y : H.Verts) (n : ℕ) (h : H.Adj x y n) :
    G.Adj x y n :=
  H.adj_sub h

theorem coe_adj_sub (H : SubTemporalGraph G) (x y : H.Verts) (n : ℕ) (h : H.coe.Adj x y n) :
    G.Adj x y n :=
  H.adj_sub h

-- Given `h : H.Adj u v t`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩ t`.
protected theorem Adj.coe {H : G.SubTemporalGraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.coe.Adj ⟨x, H.edge_vert h⟩ ⟨y, H.edge_vert' h⟩ n :=
  h

-- NOTE(refactor): `IsSubtempgraph` was renamed/reworked into `IsSubgraph`/`IsSubgraphOf` in
-- Basic.lean's "Relation rework" (independent of the Loopless/Symm split). The statement below
-- is my best guess at the intended correspondence (the original `G.IsSubtempgraph H.coe` didn't
-- even type-check against the pre-rework `IsSubtempgraph`, since `G` isn't subtype-indexed) —
-- left for review since it needs a real design decision, not just a hypothesis.
theorem coe_sub (H : SubTemporalGraph G) : H.coe.IsSubgraph G := by
  intro x y n hadj
  exact H.adj_sub hadj

section Spanning

/-- A SubTemporalGraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (H : SubTemporalGraph G) : Prop :=
  ∀ x : V, x ∈ H.Verts

theorem isSpanning_iff {H : SubTemporalGraph G} : H.IsSpanning ↔ H.Verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

end Spanning

section Props

-- Deliberately not `@[simp]`, unlike the `isSimple_iff_coe` family below: `IsSymm` is a class,
-- carried by instance resolution (see `coe_isSymm`), and rewriting it in hypothesis position
-- would only get in the way of that.
lemma isSymm_iff_coe {H : SubTemporalGraph G} : H.IsSymm ↔ H.coe.IsSymm := by
  constructor
  · intro h
    exact ⟨fun n _ _ h' ↦ h.symm n h'⟩
  · intro h
    exact ⟨fun n x y h' ↦ h.symm n (x := ⟨x, H.edge_vert h'⟩) (y := ⟨y, H.edge_vert' h'⟩) h'⟩

-- `IsSimple` is no longer redefined here; `H.IsSimple` resolves to `TemporalGraph.IsSimple
-- H.toTemporalGraph`, whose binders are EXPLICIT (unlike the old implicit-binder local
-- definition), so call sites below must supply `x y n m` explicitly.

@[simp]
lemma isSimple_iff_coe {H : SubTemporalGraph G} : H.IsSimple ↔ H.coe.IsSimple := by
  unfold TemporalGraph.IsSimple
  constructor
  · intro h _ _ _ _ h'
    exact h _ _ _ _ h'
  · intro h x y _ _ h'
    exact h ⟨x, H.edge_vert h'.1⟩ ⟨y, H.edge_vert' h'.1⟩ _ _ h'

def IsClique (H : SubTemporalGraph G) : Prop := ∀ (x y : H.Verts), x ≠ y → ∃ n, H.Adj x y n

@[simp]
lemma isClique_iff_coe {H : SubTemporalGraph G} : H.IsClique ↔ H.coe.IsClique := by
  simp only [IsClique, ne_eq, Subtype.forall, Subtype.mk.injEq, TemporalGraph.IsClique,
    coe_Adj]

-- `IsProper` is no longer redefined here; `H.IsProper` resolves to `TemporalGraph.IsProper
-- H.toTemporalGraph`, whose binders are EXPLICIT, so call sites below supply `x y z n` explicitly.

@[simp]
lemma isProper_iff_coe {H : SubTemporalGraph G} : H.IsProper ↔ H.coe.IsProper := by
  unfold TemporalGraph.IsProper
  constructor
  · intro h x y z n h'
    have := h x y z n h'
    rw [Subtype.val_inj] at this
    assumption
  · intro h x y z n h'
    have := h ⟨x, H.edge_vert h'.1⟩ ⟨y, H.edge_vert' h'.1⟩ ⟨z, H.edge_vert' h'.2⟩ n h'
    rw [←Subtype.val_inj] at this
    assumption

-- `IsHappy` is no longer redefined here; `H.IsHappy` resolves to `TemporalGraph.IsHappy
-- H.toTemporalGraph`.

@[simp]
lemma isHappy_iff_coe {H : SubTemporalGraph G} : H.IsHappy ↔ H.coe.IsHappy := by
  unfold TemporalGraph.IsHappy
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
  · intro ⟨y, n⟩ hadj ; exact H.edge_vert' hadj
  · intro ⟨y, n⟩ hyn ⟨z, m⟩ hzm heq
    simp only at heq
    subst heq
    congr
    exact h₁ x y n m ⟨hyn, hzm⟩
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

/-- The `⊤ : SubTemporalGraph G` is `G` itself. Now that symmetry is no longer a field, this
needs no hypothesis on `G` at all. -/
instance : Top G.SubTemporalGraph where
  top := {
    Verts := Set.univ
    Adj := G.Adj
    adj_sub := id
    edge_vert := @fun x _ _ _ ↦ Set.mem_univ x
    edge_vert' := @fun _ y _ _ ↦ Set.mem_univ y
  }

@[simp]
theorem top_adj {x y : V} {n : ℕ} :
    (⊤ : SubTemporalGraph G).Adj x y n ↔ G.Adj x y n :=
  Iff.rfl

theorem top_verts : (⊤ : SubTemporalGraph G).Verts = Set.univ := rfl

theorem top_toTemporalGraph : (⊤ : SubTemporalGraph G).toTemporalGraph = G := rfl

theorem top_isSpanning : (⊤ : SubTemporalGraph G).IsSpanning := by
  simp [IsSpanning, top_verts]

instance top_isSymm [hs : G.IsSymm] : (⊤ : SubTemporalGraph G).IsSymm := hs

/-- The `⊥ : SubTemporalGraph G` is the empty graph where there is no vertices. -/
instance : Bot G.SubTemporalGraph where
  bot := {
    Verts := ∅
    Adj := ⊥
    adj_sub := False.elim
    edge_vert := False.elim
    edge_vert' := False.elim
  }

instance bot_isSymm : (⊥ : SubTemporalGraph G).IsSymm := ⟨fun _ _ _ ↦ id⟩

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
    · exact ⟨h.right, h'.right⟩
    · constructor
      · intro h'' ; apply h.left ; assumption
      · intro h'' ; apply h'.left ; assumption

end Order

section Induce

/-- A SubTemporalGraph is called an *induced SubTemporalGraph* if vertices of `H` are adjacent if
they are adjacent in `G`. -/
def IsInduced (H : SubTemporalGraph G) : Prop :=
  ∀ ⦃x⦄, x ∈ H.Verts → ∀ ⦃y⦄, y ∈ H.Verts → ∀ ⦃n : ℕ⦄, G.Adj x y n → H.Adj x y n

@[simp] lemma IsInduced.top : (⊤ : G.SubTemporalGraph).IsInduced :=
  fun _ _ _ _ _ ↦ id

/-- Create the induced subgraph on `G` from another subgraph on `G`, it might not be induced to `G`.
-/
@[simps]
def induce (H : G.SubTemporalGraph) (s : Set V) : G.SubTemporalGraph where
  Verts := s
  Adj x y n := x ∈ s ∧ y ∈ s ∧ H.Adj x y n
  adj_sub h := H.adj_sub h.2.2
  edge_vert h := h.1
  edge_vert' h := h.2.1

instance induce_isSymm (H : G.SubTemporalGraph) [hs : H.IsSymm] (s : Set V) :
    (H.induce s).IsSymm :=
  ⟨fun n _ _ h ↦ ⟨h.2.1, h.1, hs.symm n h.2.2⟩⟩

lemma isInduced_of_top_induce {s : Set V} :
    (induce (⊤ : SubTemporalGraph G) s).IsInduced := by
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

instance deleteVerts_isSymm (H : SubTemporalGraph G) [H.IsSymm] (s : Set V) :
    (H.deleteVerts s).IsSymm :=
  induce_isSymm H _


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
  have hin' := hinc <| H.edge_vert' h
  exact ⟨hin, hin', h⟩

@[simp]
lemma addVerts_le {H : SubTemporalGraph G} {s : Set V} : H ≤ (H.addVerts s) := by
  constructor
  · simp
  · intro _ _ _ h ; exact addVerts_Adj h

lemma addVerts_le' (H : SubTemporalGraph G) (s : Set V) : H ≤ (H.addVerts s) := addVerts_le

instance addVerts_isSymm (H : SubTemporalGraph G) [H.IsSymm] (s : Set V) :
    (H.addVerts s).IsSymm :=
  induce_isSymm H _

end AddVerts

section AddEdge

variable {x y : V} {n : ℕ}

/-- Add the single, oriented edge `(x, y)` at time `n`. Needs no symmetry whatsoever: use
`addEdgeSymm` to add both orientations at once. -/
def addEdge (H : SubTemporalGraph G) (h : G.Adj x y n)
    (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    SubTemporalGraph G where
  Verts := H.Verts
  Adj x' y' n' := H.Adj x' y' n' ∨ (x'=x∧y'=y∧n'=n)

  edge_vert := by
    intro _ _ _ hadj
    apply hadj.elim
    · intro h' ; exact H.edge_vert h'
    · intro h' ; rw [h'.left] ; exact h₁.left

  edge_vert' := by
    intro _ _ _ hadj
    apply hadj.elim
    · intro h' ; exact H.edge_vert' h'
    · intro h' ; rw [h'.right.left] ; exact h₁.right

  adj_sub := by
    intro _ _ _ hadj
    apply hadj.elim
    · intro h' ; exact H.adj_sub h'
    · intro h' ; rwa [h'.left, h'.right.left, h'.right.right]

/-- Add both orientations of the edge between `x` and `y` at time `n`. Unlike `addEdge` this
needs `G.IsSymm`, to see the reversed orientation back in `G`. -/
def addEdgeSymm (H : SubTemporalGraph G) [G.IsSymm] (h : G.Adj x y n)
    (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    SubTemporalGraph G where
  Verts := H.Verts
  Adj x' y' n' := H.Adj x' y' n' ∨ (x'=x∧y'=y∧n'=n) ∨ (y'=x∧x'=y∧n'=n)

  edge_vert := by
    intro _ _ _ hadj
    apply hadj.elim3
    · intro h ; exact H.edge_vert h
    · intro h'' ; rw [h''.left] ; exact h₁.left
    · intro h'' ; rw [h''.right.left] ; exact h₁.right

  edge_vert' := by
    intro _ _ _ hadj
    apply hadj.elim3
    · intro h ; exact H.edge_vert' h
    · intro h'' ; rw [h''.right.left] ; exact h₁.right
    · intro h'' ; rw [h''.left] ; exact h₁.left

  adj_sub := by
    intro _ _ _ h''
    apply h''.elim3
    · intro h'' ; exact H.adj_sub h''
    · intro h'' ; rwa [h''.left.symm, h''.right.left.symm, h''.right.right.symm] at h
    · intro h'' ; rw [h''.left.symm, h''.right.left.symm, h''.right.right.symm] at h
      exact h.symm

variable {H : SubTemporalGraph G} {h : G.Adj x y n}
  {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts}

@[simp]
theorem addEdge_le : H ≤ addEdge H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

theorem addEdge_le' (H : SubTemporalGraph G) (h : G.Adj x y n)
    (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    H ≤ addEdge H h h₁ :=
  addEdge_le

@[simp]
theorem addEdge_edge : (addEdge H h h₁).Adj x y n :=
  Or.inr ⟨rfl, rfl, rfl⟩

@[simp]
theorem addEdge_verts : (addEdge H h h₁).Verts = H.Verts := rfl

@[simp]
theorem addEdgeSymm_le [G.IsSymm] : H ≤ addEdgeSymm H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

theorem addEdgeSymm_le' (H : SubTemporalGraph G) [G.IsSymm] (h : G.Adj x y n)
    (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    H ≤ addEdgeSymm H h h₁ :=
  addEdgeSymm_le

@[simp]
theorem addEdgeSymm_edge [G.IsSymm] : (addEdgeSymm H h h₁).Adj x y n :=
  Or.inr <| Or.inl ⟨rfl, rfl, rfl⟩

@[simp]
theorem addEdgeSymm_verts [G.IsSymm] : (addEdgeSymm H h h₁).Verts = H.Verts := rfl

/-- The oriented `addEdge` is the weaker of the two constructions. -/
theorem addEdge_le_addEdgeSymm [G.IsSymm] : addEdge H h h₁ ≤ addEdgeSymm H h h₁ :=
  ⟨subset_rfl, fun hadj ↦ hadj.elim Or.inl (fun h' ↦ Or.inr <| Or.inl h')⟩

instance addEdgeSymm_isSymm (H : SubTemporalGraph G) [G.IsSymm] [hsH : H.IsSymm]
    (h : G.Adj x y n) (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    (addEdgeSymm H h h₁).IsSymm := by
  constructor
  intro m _ _ hadj
  apply hadj.elim3
  · intro h' ; exact Or.inl <| hsH.symm m h'
  · intro h' ; exact Or.inr <| Or.inr h'
  · intro h' ; exact Or.inr <| Or.inl h'

end AddEdge

section EdgeProps

variable {x y : V} {n : ℕ}

-- `EarliestEdge`/`LatestEdge`/`EarliestNeighbor`/`LatestNeighbor` are no longer redefined here;
-- `H.EarliestEdge` etc. resolve to the parent `TemporalGraph` versions on `H.toTemporalGraph`.

lemma top_earliestEdge :
    (⊤ : SubTemporalGraph G).EarliestEdge x y n ↔ G.EarliestEdge x y n := by
  simp [TemporalGraph.EarliestEdge, top_adj]

lemma top_latestEdge :
    (⊤ : SubTemporalGraph G).LatestEdge x y n ↔ G.LatestEdge x y n := by
  simp [TemporalGraph.LatestEdge, top_adj]

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
  absurd (h₀ x y z n ⟨h₁.left, h₂⟩)
  exact h₄

lemma top_earliestNeighbor :
    (⊤ : SubTemporalGraph G).EarliestNeighbor x y ↔ G.EarliestNeighbor x y := by
  simp [TemporalGraph.EarliestNeighbor, top_earliestEdge]

lemma top_latestNeighbor :
    (⊤ : SubTemporalGraph G).LatestNeighbor x y ↔ G.LatestNeighbor x y := by
  simp [TemporalGraph.LatestNeighbor, top_latestEdge]

lemma earliestEdge_exists_of_nonempty_finite_incidenceSet {H : SubTemporalGraph G}
    (h₀ : (H.IncidenceSet x).Nonempty)
    (h₁ : (H.IncidenceSet x).Finite) :
    ∃ (y : V) (n : ℕ), H.EarliestEdge x y n := by
  haveI : Nonempty (H.IncidenceSet x) := Set.nonempty_coe_sort.mpr h₀
  have ⟨⟨⟨y, n⟩, hin⟩, hmin⟩ := h₁.exists_min (fun x ↦ x.1.2)
  use y, n
  unfold TemporalGraph.EarliestEdge
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
  unfold TemporalGraph.LatestEdge
  constructor
  · trivial
  · intro z m hadj
    have hin' : ⟨z, m⟩ ∈ H.IncidenceSet x := hadj
    have hle := hmax ⟨⟨z, m⟩, hin'⟩
    simp at hle
    trivial

lemma coe_earliestEdge_of_graph_earliestEdge {H : SubTemporalGraph G}
    (h₀ : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.EarliestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ n := by
  constructor
  · exact h₁
  · rw [TemporalGraph.EarliestEdge] at h₀
    rcases h₀ with ⟨hαβ, hmin⟩
    intro z m hadj
    cases z with
    | mk z hz => exact hmin z m <| H.adj_sub hadj

lemma coe_latestEdge_of_graph_latestEdge {H : SubTemporalGraph G}
    (h₀ : G.LatestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.LatestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ n := by
  constructor
  · exact h₁
  · rw [TemporalGraph.LatestEdge] at h₀
    rcases h₀ with ⟨_, hmin⟩
    intro z m hadj
    cases z with
    | mk z hz => exact hmin z m <| H.adj_sub hadj

@[simp]
lemma coe_earliestEdge {H : SubTemporalGraph G} {x y : H.Verts} {n : ℕ}
    (h₀ : H.EarliestEdge x y n) :
    H.coe.EarliestEdge x y n := by
  constructor
  · exact Adj.coe h₀.left
  · intro _ _ h
    exact h₀.right _ _ h

@[simp]
lemma earliestEdge_of_coe {H : SubTemporalGraph G} {x y : H.Verts} {n : ℕ}
    (h₀ : H.coe.EarliestEdge x y n) :
    H.EarliestEdge x y n := by
  constructor
  · exact h₀.left
  · intro _ _ h
    exact h₀.right _ _ (Adj.coe h)

lemma earliestEdge_of_graph_earliestEdge {H : SubTemporalGraph G}
    (h₀ : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.EarliestEdge x y n := by
  have h := coe_earliestEdge_of_graph_earliestEdge h₀ h₁
  exact earliestEdge_of_coe h

lemma earliestEdge_of_ge {H H' : SubTemporalGraph G} (h₀ : H ≤ H') (h₁ : H'.EarliestEdge x y n)
    (h₂ : H.Adj x y n) :
    H.EarliestEdge x y n := by
  constructor
  · trivial
  · intro _ _ h
    exact h₁.right _ _ <| h₀.right h

@[simp]
lemma coe_latestEdge {H : SubTemporalGraph G} {x y : H.Verts} {n : ℕ}
    (h₀ : H.LatestEdge x y n) :
    H.coe.LatestEdge x y n := by
  constructor
  · exact Adj.coe h₀.left
  · intro _ _ h
    exact h₀.right _ _ h

@[simp]
lemma latestEdge_of_coe {H : SubTemporalGraph G} {x y : H.Verts} {n : ℕ}
    (h₀ : H.coe.LatestEdge x y n) :
    H.LatestEdge x y n := by
  constructor
  · exact h₀.left
  · intro _ _ h
    exact h₀.right _ _ (Adj.coe h)

lemma latestEdge_of_graph_latestEdge {H : SubTemporalGraph G}
    (h₀ : G.LatestEdge x y n) (h₁ : H.Adj x y n) :
    H.LatestEdge x y n := by
  have h := coe_latestEdge_of_graph_latestEdge h₀ h₁
  exact latestEdge_of_coe h

lemma latestEdge_of_ge {H H' : SubTemporalGraph G} (h₀ : H ≤ H') (h₁ : H'.LatestEdge x y n)
    (h₂ : H.Adj x y n) :
    H.LatestEdge x y n := by
  constructor
  · trivial
  · intro _ _ h
    exact h₁.right _ _ <| h₀.right h

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
  exact H.edge_vert' h

@[simp]
lemma neighborhoodSet_iff_coe {H : SubTemporalGraph G} {x : H.Verts} :
    H.NeighborhoodSet x = H.coe.NeighborhoodSet x := by
  unfold NeighborhoodSet TemporalGraph.NeighborhoodSet
  ext y
  constructor
  · intro ⟨_, p⟩
    simp only [coe_Adj, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left,
      exists_prop, exists_eq_right_right]
    exact ⟨⟨_, p⟩, H.edge_vert' p⟩
  · intro h
    simp only [coe_Adj, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left,
      exists_prop, exists_eq_right_right] at h ⊢
    exact h.1

end NeighborHoodSet

section EdgeSet

def EdgeSet (H : SubTemporalGraph G) : Set ((Sym2 V) × ℕ) :=
  {(p, n) | ∃ x y : p, H.Adj x y n}

-- The `Adj → EdgeSet` direction is orientation-free: it just exhibits `x` and `y` as members of
-- `s(x,y)`, so it needs neither symmetry of `H` nor looplessness of `G`.
protected theorem Adj.mem_edgeSet {H : SubTemporalGraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    (s(x,y), n) ∈ H.EdgeSet :=
  ⟨⟨x, Sym2.mem_iff.mpr <| Or.inl <| Eq.refl x⟩,
    ⟨y, Sym2.mem_iff.mpr <| Or.inr <| Eq.refl y⟩, h⟩

-- `EdgeSet` is `Sym2`-valued, i.e. unordered: recognizing `s(x,y)` as an edge of `H` from the
-- reversed orientation genuinely needs `H` to be symmetric.
@[simp]
theorem mem_edgeSet (H : SubTemporalGraph G) [H.IsSymm] [G.IsLoopless]
    {x y : V} {n : ℕ} :
    (s(x,y), n) ∈ H.EdgeSet ↔ H.Adj x y n := by
  apply Iff.intro
  · intro ⟨u, v, hadj⟩
    rcases Sym2.mem_iff.mp u.prop with heq | heq
    <;> rw [heq] at hadj
    · have heq' := Sym2.mem_iff.mp v.prop |>.resolve_left (H.adj_sub hadj).ne'
      rw [heq'] at hadj
      exact hadj
    · have heq' := Sym2.mem_iff.mp v.prop |>.resolve_right (H.adj_sub hadj).ne'
      rw [heq'] at hadj
      exact H.adj_symm hadj
  · exact SubTemporalGraph.Adj.mem_edgeSet

@[simp]
lemma edgeSet_le {H : SubTemporalGraph G} {H' : SubTemporalGraph G} (h₀ : H ≤ H') :
    H.EdgeSet ⊆ H'.EdgeSet := by
  intro _ ⟨_, _, h⟩
  exact ⟨_, _, h₀.right h⟩

lemma le_iff_edgeSet_and_verts {H H' : SubTemporalGraph G} [H'.IsSymm]
    [G.IsLoopless] :
    H ≤ H' ↔ H.EdgeSet ⊆ H'.EdgeSet ∧ H.Verts ⊆ H'.Verts := by
  constructor
  · intro h
    constructor
    · apply edgeSet_le h
    · exact h.left
  · intro h
    constructor
    · exact h.right
    · intro _ _ _ hadj
      rw [←mem_edgeSet H']
      exact Set.mem_of_subset_of_mem h.left (Adj.mem_edgeSet hadj)

@[simp]
lemma addEdgeSymm_edgeSet (H : SubTemporalGraph G) {x y : V} {n : ℕ}
    [G.IsSymm] [G.IsLoopless]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts} :
    (H.addEdgeSymm h₀ h₁).EdgeSet = insert ⟨s(x,y), n⟩ H.EdgeSet := by
  unfold addEdgeSymm EdgeSet
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

lemma addEdgeSymm_edgeSet' (H : SubTemporalGraph G) {x y : V} {n : ℕ}
    [G.IsSymm] [G.IsLoopless]
    (h₀ : G.Adj x y n)
    (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts) :
    (H.addEdgeSymm h₀ h₁).EdgeSet = insert ⟨s(x,y), n⟩ H.EdgeSet :=
  H.addEdgeSymm_edgeSet

instance {H : SubTemporalGraph G} [h : Finite H.EdgeSet] {x y : V} {n : ℕ}
    [G.IsSymm] [G.IsLoopless]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts} :
    Finite (H.addEdgeSymm h₀ h₁).EdgeSet := by
  conv =>
    rhs ; rw [H.addEdgeSymm_edgeSet, ←Set.union_singleton]
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
    use x, Or.inl (H.edge_vert hadj), hx, y, Or.inl (H.edge_vert' hadj)

lemma addVerts_edgeSet' {H : SubTemporalGraph G} (s : Set V) :
    (H.addVerts s).EdgeSet = H.EdgeSet := addVerts_edgeSet

instance {H : SubTemporalGraph G} {s : Set V} [h₀ : Finite H.EdgeSet] [Finite s] :
    Finite (H.addVerts s).EdgeSet := by
  simp only [addVerts_edgeSet, h₀]

theorem edgeSet_toTemporalGraph {H : SubTemporalGraph G} :
    H.EdgeSet = H.toTemporalGraph.EdgeSet := rfl

def FootprintEdgeSet (H : SubTemporalGraph G) : Set (Sym2 V) :=
  {p | ∃ n : ℕ, ∃ x y : p, H.Adj x y n}

-- NOTE(refactor): `Footprint` now returns a Mathlib `Digraph` (Basic.lean's "Relation rework"),
-- which has no `edgeSet` (directed graphs don't have unordered edges) — unlike the old
-- `SimpleGraph`-valued `Footprint`. This statement can't even be typed as-is anymore; left for
-- review (likely needs restating via `Footprint.Adj` or `SimpleGraph.fromRel` instead of
-- `.edgeSet`).
-- theorem FootprintEdgeSet_eq {H : SubTemporalGraph G} (hl : G.IsLoopless) :
--     H.toTemporalGraph.Footprint.edgeSet = H.FootprintEdgeSet := by
--   sorry

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

lemma edgeSetToFootprintEdgeSet_injective (H : SubTemporalGraph G) [H.IsSymm]
    [G.IsLoopless]
    (h₀ : H.IsSimple) :
    Function.Injective H.EdgeSetToFootprintEdgeSet := by
  intro x y h
  have ⟨a, b, hadj⟩ := x.prop
  have ⟨a', b', hadj'⟩ := y.prop
  simp only [EdgeSetToFootprintEdgeSet, Subtype.mk.injEq] at h
  ext
  · apply Sym2.ext_iff.mp h
  · refine h₀ a b x.1.2 y.1.2 ⟨hadj, ?_⟩
    have hxs := x.1.1.mem_and_mem_iff (H.adj_sub hadj).ne |>.mp ⟨a.prop, b.prop⟩
    have hys := y.1.1.mem_and_mem_iff (H.adj_sub hadj').ne |>.mp ⟨a'.prop, b'.prop⟩
    rw [hxs, hys] at h
    rcases Sym2.eq_iff.mp h with heq | heq
    · rw [heq.1.symm, heq.2.symm] at hadj'
      exact hadj'
    · rw [heq.1.symm, heq.2.symm] at hadj'
      exact H.adj_symm hadj'

lemma edgeSetToFootprintEdgeSet_bijective (H : SubTemporalGraph G) [H.IsSymm]
    [G.IsLoopless]
    (h₀ : H.IsSimple) :
    Function.Bijective H.EdgeSetToFootprintEdgeSet :=
  ⟨H.edgeSetToFootprintEdgeSet_injective h₀, H.edgeSetToFootprintEdgeSet_surjective⟩

end EdgeSet

section Size

def size (H : SubTemporalGraph G) [Fintype H.EdgeSet] := Fintype.card H.EdgeSet

def order (H : SubTemporalGraph G) [Fintype H.Verts] := Fintype.card H.Verts

lemma size_of_simple (H : SubTemporalGraph G)
    [Fintype H.EdgeSet]
    [Fintype H.FootprintEdgeSet]
    [H.IsSymm]
    [G.IsLoopless]
    (h₀ : H.IsSimple) :
    H.size = Fintype.card H.FootprintEdgeSet := by
  apply Fintype.card_of_bijective (f := H.EdgeSetToFootprintEdgeSet)
  exact H.edgeSetToFootprintEdgeSet_bijective h₀

lemma size_of_toTemporalGraph (H : SubTemporalGraph G)
    [Fintype H.EdgeSet]
    [Fintype H.toTemporalGraph.EdgeSet] :
    H.size = H.toTemporalGraph.size := by
  unfold size TemporalGraph.size
  rw [←Nat.card_eq_fintype_card, ←Nat.card_eq_fintype_card, edgeSet_toTemporalGraph]

-- NOTE(refactor): `Finite → Fintype` isn't automatic in Mathlib (avoids diamonds), so the
-- `Finite` instance above does not chain into a `Fintype` one on its own: callers must supply
-- the `Fintype` instance explicitly.
theorem addEdgeSymm_size (H : SubTemporalGraph G) {x y : V} {n : ℕ}
    [H.IsSymm] [G.IsSymm] [G.IsLoopless]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts}
    {h₂ : ¬H.Adj x y n}
    [Fintype H.EdgeSet] [Fintype (H.addEdgeSymm h₀ h₁).EdgeSet] :
    (H.addEdgeSymm h₀ h₁).size = H.size + 1 := by
  simp only [size, H.addEdgeSymm_edgeSet, H.mem_edgeSet, h₂, not_false_eq_true,
    Set.card_insert]

@[simp]
theorem addEdgeSymm_size_le (H : SubTemporalGraph G) {x y : V} {n : ℕ}
    [G.IsSymm] [G.IsLoopless]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.Verts ∧ y ∈ H.Verts}
    [Fintype H.EdgeSet] [Fintype (H.addEdgeSymm h₀ h₁).EdgeSet] :
    (H.addEdgeSymm h₀ h₁).size ≤ H.size + 1 := by
  unfold size
  have h : (H.addEdgeSymm h₀ h₁).EdgeSet = H.EdgeSet ∪ {(s(x,y), n)} := by
    simp only [H.addEdgeSymm_edgeSet, Set.union_singleton]
  have h' := Set.card_union_le H.EdgeSet {(s(x,y), n)}
  simp only [h, Nat.card_eq_fintype_card, Set.card_singleton] at h' ⊢
  assumption

theorem addEdgeSymm_size_le' (H : SubTemporalGraph G) {x y : V} {n : ℕ}
    [G.IsSymm] [G.IsLoopless]
    (h₀ : G.Adj x y n)
    (h₁ : x ∈ H.Verts ∧ y ∈ H.Verts)
    [Fintype H.EdgeSet] [Fintype (H.addEdgeSymm h₀ h₁).EdgeSet] :
    Fintype.card (H.addEdgeSymm h₀ h₁).EdgeSet ≤ Fintype.card H.EdgeSet + 1 := by
  exact H.addEdgeSymm_size_le

@[simp]
theorem addVerts_size {H : SubTemporalGraph G} {s : Set V}
    [Fintype H.EdgeSet]
    [Fintype (H.addVerts s).EdgeSet] :
    Fintype.card (H.addVerts s).EdgeSet = Fintype.card H.EdgeSet := by
  simp only [addVerts_edgeSet]

end Size

end SubTemporalGraph

namespace NonemptyTemporalWalk

variable {V : Type u} {G : TemporalGraph V}

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
protected def lift_subTemporalGraph_walk {H : SubTemporalGraph G} {H' : SubTemporalGraph G}
    {x y : H.Verts}
    {n m : ℕ}
    (h : H ≤ H') :
    H.coe.NonemptyTemporalWalk x n y m → H'.coe.NonemptyTemporalWalk
      ⟨x, Set.mem_of_subset_of_mem h.left x.prop⟩ n
      ⟨y, Set.mem_of_subset_of_mem h.left y.prop⟩ m
  | Single h' => Single (h.right h')
  | Step p h' hle =>
    Step (p.lift_subTemporalGraph_walk h)
      (SubTemporalGraph.Adj.coe (h.right h'))
      hle

@[coe]
protected def lift_toTemporalGraph_walk {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    H.toTemporalGraph.NonemptyTemporalWalk x n y m → H.coe.NonemptyTemporalWalk x n y m
  | Single h => @Single H.Verts H.coe x y n h
  | @Step _ _ _ y' _ _ m' _ p' h' hle' =>
      @Step H.Verts H.coe x ⟨y', H.edge_vert h'⟩ y n m' m
        (p'.lift_toTemporalGraph_walk)
        h' hle'

instance {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    Coe (H.toTemporalGraph.NonemptyTemporalWalk x n y m) (H.coe.NonemptyTemporalWalk x n y m) where
  coe p := p.lift_toTemporalGraph_walk

@[coe]
protected def lift_walk_toTemporalGraph {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    H.coe.NonemptyTemporalWalk x n y m → H.toTemporalGraph.NonemptyTemporalWalk ↑x n ↑y m
  | Single h => Single h
  | Step p h h' => Step p.lift_walk_toTemporalGraph h h'

instance {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    Coe (H.coe.NonemptyTemporalWalk x n y m)
      (H.toTemporalGraph.NonemptyTemporalWalk ↑x n ↑y m) where
  coe p := p.lift_walk_toTemporalGraph

end NonemptyTemporalWalk

namespace TemporalWalk

variable {V : Type u} {G : TemporalGraph V} {H : SubTemporalGraph G}

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
  | Nonempty p => Nonempty <| p.lift_subTemporalGraph_walk h

@[coe]
protected def lift_toTemporalGraph_walk {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ}
    (w : H.toTemporalGraph.TemporalWalk ↑x n ↑y m) : H.coe.TemporalWalk x n y m := by
  obtain ⟨xv, hx⟩ := x
  obtain ⟨yv, hy⟩ := y
  simp only at w ⊢
  cases w with
  | Empty =>
    exact .Empty
  | Nonempty p =>
    exact .Nonempty p.lift_toTemporalGraph_walk

instance {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    Coe (H.toTemporalGraph.TemporalWalk x n y m) (H.coe.TemporalWalk x n y m) where
  coe p := p.lift_toTemporalGraph_walk

@[coe]
protected def lift_walk_toTemporalGraph {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    H.coe.TemporalWalk x n y m → H.toTemporalGraph.TemporalWalk ↑x n ↑y m
  | Empty => Empty
  | Nonempty p => Nonempty p.lift_walk_toTemporalGraph

instance {H : SubTemporalGraph G} {x y : H.Verts} {n m : ℕ} :
    Coe (H.coe.TemporalWalk x n y m) (H.toTemporalGraph.TemporalWalk ↑x n ↑y m) where
  coe p := p.lift_walk_toTemporalGraph


end TemporalWalk

section SubgraphProps

variable {V : Type u} {G : TemporalGraph V}

-- `@[simps!]` alone chokes on the `Adj` field here: it is given as the bare projection `H.Adj`
-- of an opaque parameter `H`, so simps cannot unfold it any further to a constructor application.
-- Restricting the auto-generated lemmas to `Verts` and restating `Adj` by hand avoids the issue.
@[simps! Verts]
def toSubTemporalGraph (H : TemporalGraph V) (h : H ≤ G) : G.SubTemporalGraph where
  Verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  edge_vert' _ := Set.mem_univ _

@[simp]
theorem toSubTemporalGraph_Adj (H : TemporalGraph V) (h : H ≤ G) {x y : V} {n : ℕ} :
    (toSubTemporalGraph H h).Adj x y n ↔ H.Adj x y n :=
  Iff.rfl

theorem toSubgraph.isSpanning (H : TemporalGraph V) (h : H ≤ G) :
    (toSubTemporalGraph H h).IsSpanning :=
  Set.mem_univ

instance toSubTemporalGraph_isSymm (H : TemporalGraph V) [hs : H.IsSymm] (h : H ≤ G) :
    (toSubTemporalGraph H h).IsSymm :=
  hs

def toSubgraphTop : G.SubTemporalGraph := ⊤

/-- Create a `SubTemporalGraph G` from a set of edges, the edges not in `G.EdgeSet` are ignored. -/
@[simps!]
def fromEdgeSet (G : TemporalGraph V) (s : Set ((Sym2 V) × ℕ)) :
    SubTemporalGraph G where
  Verts := {x | ∃ (p : s) , x ∈ p.1.1 }
  Adj x y n := ∃ (a : s), x ∈ a.1.1 ∧ y ∈ a.1.1 ∧ n = a.1.2 ∧ G.Adj x y n

  adj_sub h := by
    have ⟨_, h⟩ := h
    exact h.2.2.2

  edge_vert h := by
    obtain ⟨a, h⟩ := h
    use a
    exact h.1

  edge_vert' h := by
    obtain ⟨a, h⟩ := h
    use a
    exact h.2.1

instance fromEdgeSet_isSymm (G : TemporalGraph V) [G.IsSymm] (s : Set ((Sym2 V) × ℕ)) :
    (G.fromEdgeSet s).IsSymm := by
  constructor
  intro _ _ _ h
  simp only [fromEdgeSet, Subtype.exists, exists_and_left, exists_prop, Prod.exists, ↓existsAndEq,
    true_and] at ⊢ h
  obtain ⟨a, h⟩ := h
  use a
  simp only [h, h.2.2.2.symm, and_self]

@[simp]
theorem fromEdgeSet_eq {G : TemporalGraph V} [G.IsSymm] [G.IsLoopless]
    {s : Set ((Sym2 V) × ℕ)} (h₀ : s ⊆ G.EdgeSet) :
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
    simp only [Sym2.mem_iff, true_or, exists_eq_or_imp, TemporalGraph.irrefl, and_false,
      exists_false, ↓existsAndEq, true_and, false_or]
    use s(x,y)
    simp only [Sym2.mem_iff, true_or, or_true, ha, true_and]
    rw [←TemporalGraph.mem_edgeSet G]
    have : (s(x,y), n) ∈ s := by simp only [ha]
    apply Set.mem_of_subset_of_mem h₀ this


end SubgraphProps

end TemporalGraph
