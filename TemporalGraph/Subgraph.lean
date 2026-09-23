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
structure Subgraph {V : Type u} (G : TemporalGraph V) extends TemporalGraph V where
  verts : Set V

  adj_sub : ∀ {x y : V} {n : ℕ}, Adj x y n → G.Adj x y n
  edge_vert : ∀ {x y : V} {n : ℕ}, Adj x y n → x ∈ verts
  edge_vert' : ∀ {x y : V} {n : ℕ}, Adj x y n → y ∈ verts

namespace Subgraph

variable {V : Type u} {G : TemporalGraph V}

-- `IsSymm` is no longer redefined here: `Subgraph` now `extends TemporalGraph V`, so
-- `H.IsSymm` resolves through generalized field notation to
-- `TemporalGraph.IsSymm H.toTemporalGraph`.

/-- A subgraph of a loopless graph is loopless: an instance, so that `[G.IsLoopless]` alone
suffices at every use site, however deeply the subgraph is built up. -/
instance loopless (H : Subgraph G) [G.IsLoopless] : H.IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩⟩

@[simp]
protected theorem irrefl {H : Subgraph G} [G.IsLoopless] {x : V} {n : ℕ} :
    ¬H.Adj x x n :=
  TemporalGraph.irrefl

theorem adj_comm (H : Subgraph G) [hs : H.IsSymm] (x y : V) (n : ℕ) :
    H.Adj x y n ↔ H.Adj y x n :=
  ⟨fun h ↦ hs.symm n h, fun h ↦ hs.symm n h⟩

-- No `@[symm]`: `TemporalGraph.adj_symm` already carries the attribute and applies here, since
-- `H.Adj` *is* `H.toTemporalGraph.Adj`.
theorem adj_symm (H : Subgraph G) [hs : H.IsSymm] {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.Adj y x n :=
  hs.symm n h

protected theorem Adj.symm {H : Subgraph G} [hs : H.IsSymm] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    H.Adj y x n :=
  hs.symm n h

protected theorem Adj.adj_sub {H : G.Subgraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    G.Adj u v t :=
  H.adj_sub h

protected theorem Adj.ne {H : Subgraph G} [G.IsLoopless] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    x ≠ y :=
  (H.adj_sub h).ne

protected theorem Adj.ne' {H : Subgraph G} [G.IsLoopless] {x y : V} {n : ℕ}
    (h : H.Adj x y n) :
    y ≠ x :=
  (H.adj_sub h).ne'

protected theorem Adj.fst_mem {H : G.Subgraph} {u v : V} {t : ℕ} (h : H.Adj u v t) :
    u ∈ H.verts :=
  H.edge_vert h

protected theorem Adj.snd_mem {H : G.Subgraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    y ∈ H.verts :=
  H.edge_vert' h

/-- Coercion from `H : Subgraph G` to a `TemporalGraph H.verts`. -/
@[simps, coe]
protected def coe (H : Subgraph G) : TemporalGraph H.verts where
  Adj x y n := H.Adj x y n

instance coe_isSymm (H : Subgraph G) [hs : H.IsSymm] : H.coe.IsSymm :=
  ⟨fun n _ _ h ↦ hs.symm n h⟩

instance coe_isLoopless (H : Subgraph G) [G.IsLoopless] : H.coe.IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ G.irrefl (H.adj_sub h)⟩⟩

@[simp]
theorem Adj.adj_sub' (H : Subgraph G) (x y : H.verts) (n : ℕ) (h : H.Adj x y n) :
    G.Adj x y n :=
  H.adj_sub h

theorem coe_adj_sub (H : Subgraph G) (x y : H.verts) (n : ℕ) (h : H.coe.Adj x y n) :
    G.Adj x y n :=
  H.adj_sub h

-- Given `h : H.Adj u v t`, then `h.coe : H.coe.Adj ⟨u, _⟩ ⟨v, _⟩ t`.
protected theorem Adj.coe {H : G.Subgraph} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    H.coe.Adj ⟨x, H.edge_vert h⟩ ⟨y, H.edge_vert' h⟩ n :=
  h

/-- The subtype view of a subgraph is a subgraph of the ambient graph, in the general sense of
`TemporalGraph.IsSubgraphOf`: its vertices are vertices of `G`, and its adjacencies are `G`'s. -/
theorem coe_sub (H : Subgraph G) :
    IsSubgraphOf H.coe (G : TemporalGraph {x : V // True}) where
  incl _ _ := trivial
  incl' hadj := H.adj_sub hadj

section Spanning

/-- A Subgraph is called a *spanning subgraph* if it contains all the vertices of `G`. -/
def IsSpanning (H : Subgraph G) : Prop :=
  ∀ x : V, x ∈ H.verts

theorem isSpanning_iff {H : Subgraph G} : H.IsSpanning ↔ H.verts = Set.univ :=
  Set.eq_univ_iff_forall.symm

end Spanning

section Props

-- Deliberately not `@[simp]`, unlike the `isSimple_iff_coe` family below: `IsSymm` is a class,
-- carried by instance resolution (see `coe_isSymm`), and rewriting it in hypothesis position
-- would only get in the way of that.
lemma isSymm_iff_coe {H : Subgraph G} : H.IsSymm ↔ H.coe.IsSymm := by
  constructor
  · intro h
    exact ⟨fun n _ _ h' ↦ h.symm n h'⟩
  · intro h
    exact ⟨fun n x y h' ↦ h.symm n (x := ⟨x, H.edge_vert h'⟩) (y := ⟨y, H.edge_vert' h'⟩) h'⟩

-- `IsSimple` is no longer redefined here; `H.IsSimple` resolves to `TemporalGraph.IsSimple
-- H.toTemporalGraph`, whose binders are EXPLICIT (unlike the old implicit-binder local
-- definition), so call sites below must supply `x y n m` explicitly.

@[simp]
lemma isSimple_iff_coe {H : Subgraph G} : H.IsSimple ↔ H.coe.IsSimple := by
  unfold TemporalGraph.IsSimple
  constructor
  · intro h _ _ _ _ h'
    exact h _ _ _ _ h'
  · intro h x y _ _ h'
    exact h ⟨x, H.edge_vert h'.1⟩ ⟨y, H.edge_vert' h'.1⟩ _ _ h'

def IsClique (H : Subgraph G) : Prop := ∀ (x y : H.verts), x ≠ y → ∃ n, H.Adj x y n

@[simp]
lemma isClique_iff_coe {H : Subgraph G} : H.IsClique ↔ H.coe.IsClique := by
  simp only [IsClique, ne_eq, Subtype.forall, Subtype.mk.injEq, TemporalGraph.IsClique,
    coe_Adj]

-- `IsProper` is no longer redefined here; `H.IsProper` resolves to `TemporalGraph.IsProper
-- H.toTemporalGraph`, whose binders are EXPLICIT, so call sites below supply `x y z n` explicitly.

@[simp]
lemma isProper_iff_coe {H : Subgraph G} : H.IsProper ↔ H.coe.IsProper := by
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
lemma isHappy_iff_coe {H : Subgraph G} : H.IsHappy ↔ H.coe.IsHappy := by
  unfold TemporalGraph.IsHappy
  simp only [isSimple_iff_coe, isProper_iff_coe]

instance [Finite V] {H : Subgraph G} : Finite H.verts :=
  H.verts.toFinite


-- From SimpleGraph.Subgraph.IsMatching Revised
def IsMatching (M : Subgraph G) : Prop :=
  ∀ ⦃v : V⦄, v ∈ M.verts → ∃! q : V × ℕ, M.Adj v q.1 q.2

-- From SimpleGraph.Subgraph.IsPerfectMatching
def IsPerfectMatching (M : Subgraph G) := M.IsMatching ∧ M.IsSpanning

def IsPerfectMatchingOf (M : Subgraph G) (H : Subgraph G) :=
  M.IsMatching ∧ M.verts = H.verts

end Props

section incidenceSet

def incidenceSet (H : Subgraph G) (x : V) : Set (V × ℕ) :=
  { (y, n) : V × ℕ | H.Adj x y n }

lemma finite_incidenceSet_of_finite_simple {H : Subgraph G} [h : Finite H.verts]
    (h₁ : H.IsSimple) :
    ∀ (x : H.verts), (H.incidenceSet x).Finite := by
  intro x
  apply Set.Finite.of_injOn (f := fun p : V × ℕ => p.1) (t := H.verts)
  · intro ⟨y, n⟩ hadj ; exact H.edge_vert' hadj
  · intro ⟨y, n⟩ hyn ⟨z, m⟩ hzm heq
    simp only at heq
    subst heq
    congr
    exact h₁ x y n m ⟨hyn, hzm⟩
  · exact h

instance {H : Subgraph G} [Finite H.verts] {h₀ : H.IsSimple} {x : H.verts} :
    Finite (H.incidenceSet x) :=
  finite_incidenceSet_of_finite_simple h₀ x

lemma nonempty_incidenceSet_of_nontrivial_clique {H : Subgraph G} [h : Nontrivial H.verts]
    (h₁ : H.IsClique) :
    ∀ x : H.verts, (H.incidenceSet x).Nonempty := by
  intro x
  have ⟨y, z, hne⟩ := h.exists_pair_ne
  by_cases heq : x=y
  · subst heq
    have ⟨n, hadj⟩ := h₁ x z hne
    have h' : ⟨z, n⟩ ∈ (H.incidenceSet x) := hadj
    use ⟨z, n⟩
  · have ⟨n, hadj⟩ := h₁ x y heq
    have h' : ⟨y, n⟩ ∈ (H.incidenceSet x) := hadj
    use ⟨y, n⟩

end incidenceSet

section Order

/-- The `⊤ : Subgraph G` is `G` itself. Now that symmetry is no longer a field, this
needs no hypothesis on `G` at all. -/
instance : Top G.Subgraph where
  top := {
    verts := Set.univ
    Adj := G.Adj
    adj_sub := id
    edge_vert := @fun x _ _ _ ↦ Set.mem_univ x
    edge_vert' := @fun _ y _ _ ↦ Set.mem_univ y
  }

@[simp]
theorem top_adj {x y : V} {n : ℕ} :
    (⊤ : Subgraph G).Adj x y n ↔ G.Adj x y n :=
  Iff.rfl

theorem top_verts : (⊤ : Subgraph G).verts = Set.univ := rfl

theorem top_toTemporalGraph : (⊤ : Subgraph G).toTemporalGraph = G := rfl

theorem top_isSpanning : (⊤ : Subgraph G).IsSpanning := by
  simp [IsSpanning, top_verts]

instance top_isSymm [hs : G.IsSymm] : (⊤ : Subgraph G).IsSymm := hs

/-- The `⊥ : Subgraph G` is the empty graph where there is no vertices. -/
instance : Bot G.Subgraph where
  bot := {
    verts := ∅
    Adj := ⊥
    adj_sub := False.elim
    edge_vert := False.elim
    edge_vert' := False.elim
  }

instance bot_isSymm : (⊥ : Subgraph G).IsSymm := ⟨fun _ _ _ ↦ id⟩

/-- `H ≤ H'` when `H`'s vertices are among `H'`'s and every adjacency of `H` is one of `H'`.
Written directly into the instance, as `SimpleGraph.Subgraph` does, rather than through a named
relation that would compete with `TemporalGraph.IsSubgraphOf`. -/
instance : LE (Subgraph G) :=
  ⟨fun H H' => H.verts ⊆ H'.verts ∧ ∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n⟩

instance : BoundedOrder (Subgraph G) where
  top := ⊤
  bot := ⊥
  le_top x := ⟨Set.subset_univ _, by intro _ _ _ h ; rw [top_adj] ; exact x.adj_sub h⟩
  bot_le _ := ⟨Set.empty_subset _, False.elim⟩

instance : LT (Subgraph G) where
  lt H H' :=
    ((H.verts ⊂ H'.verts) ∧ (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n))
    ∨
    ((H.verts = H'.verts) ∧ (∀ {x y : V} {n : ℕ}, H.Adj x y n → H'.Adj x y n)
      ∧ (∃ (x y : V) (n : ℕ), H'.Adj x y n ∧ ¬ H.Adj x y n))

instance : Preorder (Subgraph G) where
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
          · have h := h.right ; dsimp [LE.le] at h ; push_neg at h
            exact h h'.symm.subset
      · intro h' ; left ; constructor
        · assumption
        · exact h.left.right

instance : PartialOrder (Subgraph G) where
  le_antisymm A B h h' := by
    ext _ _ _
    · exact ⟨h.right, h'.right⟩
    · constructor
      · intro h'' ; apply h.left ; assumption
      · intro h'' ; apply h'.left ; assumption

end Order

section Induce

/-- A Subgraph is called an *induced Subgraph* if vertices of `H` are adjacent if
they are adjacent in `G`. -/
def IsInduced (H : Subgraph G) : Prop :=
  ∀ ⦃x⦄, x ∈ H.verts → ∀ ⦃y⦄, y ∈ H.verts → ∀ ⦃n : ℕ⦄, G.Adj x y n → H.Adj x y n

@[simp] lemma IsInduced.top : (⊤ : G.Subgraph).IsInduced :=
  fun _ _ _ _ _ ↦ id

/-- Create the induced subgraph on `G` from another subgraph on `G`, it might not be induced to `G`.
-/
@[simps]
def induce (H : G.Subgraph) (s : Set V) : G.Subgraph where
  verts := s
  Adj x y n := x ∈ s ∧ y ∈ s ∧ H.Adj x y n
  adj_sub h := H.adj_sub h.2.2
  edge_vert h := h.1
  edge_vert' h := h.2.1

instance induce_isSymm (H : G.Subgraph) [hs : H.IsSymm] (s : Set V) :
    (H.induce s).IsSymm :=
  ⟨fun n _ _ h ↦ ⟨h.2.1, h.1, hs.symm n h.2.2⟩⟩

lemma isInduced_of_top_induce {s : Set V} :
    (induce (⊤ : Subgraph G) s).IsInduced := by
  intro x hx y hy n h
  refine ⟨hx, hy, h⟩

end Induce

section DeleteVerts

abbrev deleteVerts (H : Subgraph G) (s : Set V) : G.Subgraph :=
  H.induce (H.verts \ s)

lemma deleteVerts_verts (H : Subgraph G) (s : Set V) :
    (H.deleteVerts s).verts = H.verts \ s :=
  rfl

@[simp]
theorem deleteVerts_le {H : Subgraph G} {s : Set V} : (H.deleteVerts s) ≤ H := by
  constructor <;> simp [Set.diff_subset]

theorem deleteVerts_le' (H : Subgraph G) (s : Set V) : (H.deleteVerts s) ≤ H := by
  constructor <;> simp [Set.diff_subset]

instance deleteVerts_isSymm (H : Subgraph G) [H.IsSymm] (s : Set V) :
    (H.deleteVerts s).IsSymm :=
  induce_isSymm H _


end DeleteVerts

section AddVerts

abbrev addVerts (H : Subgraph G) (s : Set V) : G.Subgraph :=
  H.induce (H.verts ∪ s)

@[simp]
lemma addVerts_verts (H : Subgraph G) (s : Set V) : (H.addVerts s).verts = H.verts ∪ s :=
  rfl

lemma addVerts_Adj {x y : V} {n : ℕ} {H : Subgraph G} {s : Set V} :
    H.Adj x y n → (H.addVerts s).Adj x y n := by
  have hinc : H.verts ⊆ (H.addVerts s).verts := by simp
  intro h
  have hin := hinc <| H.edge_vert h
  have hin' := hinc <| H.edge_vert' h
  exact ⟨hin, hin', h⟩

@[simp]
lemma addVerts_le {H : Subgraph G} {s : Set V} : H ≤ (H.addVerts s) := by
  constructor
  · simp
  · intro _ _ _ h ; exact addVerts_Adj h

lemma addVerts_le' (H : Subgraph G) (s : Set V) : H ≤ (H.addVerts s) := addVerts_le

instance addVerts_isSymm (H : Subgraph G) [H.IsSymm] (s : Set V) :
    (H.addVerts s).IsSymm :=
  induce_isSymm H _

end AddVerts

section AddEdge

variable {x y : V} {n : ℕ}

/-- Add the single, oriented edge `(x, y)` at time `n`. Needs no symmetry whatsoever: use
`addEdgeSymm` to add both orientations at once. -/
def addEdge (H : Subgraph G) (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    Subgraph G where
  verts := H.verts
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
def addEdgeSymm (H : Subgraph G) [G.IsSymm] (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    Subgraph G where
  verts := H.verts
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

variable {H : Subgraph G} {h : G.Adj x y n}
  {h₁ : x ∈ H.verts ∧ y ∈ H.verts}

@[simp]
theorem addEdge_le : H ≤ addEdge H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

theorem addEdge_le' (H : Subgraph G) (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    H ≤ addEdge H h h₁ :=
  addEdge_le

@[simp]
theorem addEdge_edge : (addEdge H h h₁).Adj x y n :=
  Or.inr ⟨rfl, rfl, rfl⟩

@[simp]
theorem addEdge_verts : (addEdge H h h₁).verts = H.verts := rfl

@[simp]
theorem addEdgeSymm_le [G.IsSymm] : H ≤ addEdgeSymm H h h₁ := by
  constructor
  · intro _ hx
    exact hx
  · intro _ _ _ hadj
    exact Or.inl hadj

theorem addEdgeSymm_le' (H : Subgraph G) [G.IsSymm] (h : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    H ≤ addEdgeSymm H h h₁ :=
  addEdgeSymm_le

@[simp]
theorem addEdgeSymm_edge [G.IsSymm] : (addEdgeSymm H h h₁).Adj x y n :=
  Or.inr <| Or.inl ⟨rfl, rfl, rfl⟩

@[simp]
theorem addEdgeSymm_verts [G.IsSymm] : (addEdgeSymm H h h₁).verts = H.verts := rfl

/-- The oriented `addEdge` is the weaker of the two constructions. -/
theorem addEdge_le_addEdgeSymm [G.IsSymm] : addEdge H h h₁ ≤ addEdgeSymm H h h₁ :=
  ⟨subset_rfl, fun hadj ↦ hadj.elim Or.inl (fun h' ↦ Or.inr <| Or.inl h')⟩

instance addEdgeSymm_isSymm (H : Subgraph G) [G.IsSymm] [hsH : H.IsSymm]
    (h : G.Adj x y n) (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
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
    (⊤ : Subgraph G).EarliestEdge x y n ↔ G.EarliestEdge x y n := by
  simp [TemporalGraph.EarliestEdge, top_adj]

lemma top_latestEdge :
    (⊤ : Subgraph G).LatestEdge x y n ↔ G.LatestEdge x y n := by
  simp [TemporalGraph.LatestEdge, top_adj]

@[simp]
lemma earliestEdge_lt_of_proper {H : Subgraph G} {z : V} {m : ℕ}
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
    (⊤ : Subgraph G).EarliestNeighbor x y ↔ G.EarliestNeighbor x y := by
  simp [TemporalGraph.EarliestNeighbor, top_earliestEdge]

lemma top_latestNeighbor :
    (⊤ : Subgraph G).LatestNeighbor x y ↔ G.LatestNeighbor x y := by
  simp [TemporalGraph.LatestNeighbor, top_latestEdge]

lemma earliestEdge_exists_of_nonempty_finite_incidenceSet {H : Subgraph G}
    (h₀ : (H.incidenceSet x).Nonempty)
    (h₁ : (H.incidenceSet x).Finite) :
    ∃ (y : V) (n : ℕ), H.EarliestEdge x y n := by
  haveI : Nonempty (H.incidenceSet x) := Set.nonempty_coe_sort.mpr h₀
  have ⟨⟨⟨y, n⟩, hin⟩, hmin⟩ := h₁.exists_min (fun x ↦ x.1.2)
  use y, n
  unfold TemporalGraph.EarliestEdge
  constructor
  · trivial
  · intro z m hadj
    have hin' : ⟨z, m⟩ ∈ H.incidenceSet x := hadj
    have hle := hmin ⟨⟨z, m⟩, hin'⟩
    simp at hle
    trivial

lemma latestEdge_exists_of_nonempty_finite_incidenceSet {H : Subgraph G}
    (h₀ : (H.incidenceSet x).Nonempty)
    (h₁ : (H.incidenceSet x).Finite) :
    ∃ (z : V) (m : ℕ), H.LatestEdge x z m := by
  haveI : Nonempty (H.incidenceSet x) := Set.nonempty_coe_sort.mpr h₀
  have ⟨⟨⟨y, n⟩, hin⟩, hmax⟩ := h₁.exists_max (fun x ↦ x.1.2)
  use y, n
  unfold TemporalGraph.LatestEdge
  constructor
  · trivial
  · intro z m hadj
    have hin' : ⟨z, m⟩ ∈ H.incidenceSet x := hadj
    have hle := hmax ⟨⟨z, m⟩, hin'⟩
    simp at hle
    trivial

lemma coe_earliestEdge_of_graph_earliestEdge {H : Subgraph G}
    (h₀ : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.coe.EarliestEdge ⟨x, H.edge_vert h₁⟩ ⟨y, H.edge_vert' h₁⟩ n := by
  constructor
  · exact h₁
  · rw [TemporalGraph.EarliestEdge] at h₀
    rcases h₀ with ⟨hαβ, hmin⟩
    intro z m hadj
    cases z with
    | mk z hz => exact hmin z m <| H.adj_sub hadj

lemma coe_latestEdge_of_graph_latestEdge {H : Subgraph G}
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
lemma coe_earliestEdge {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.EarliestEdge x y n) :
    H.coe.EarliestEdge x y n := by
  constructor
  · exact Adj.coe h₀.left
  · intro _ _ h
    exact h₀.right _ _ h

@[simp]
lemma earliestEdge_of_coe {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.coe.EarliestEdge x y n) :
    H.EarliestEdge x y n := by
  constructor
  · exact h₀.left
  · intro _ _ h
    exact h₀.right _ _ (Adj.coe h)

lemma earliestEdge_of_graph_earliestEdge {H : Subgraph G}
    (h₀ : G.EarliestEdge x y n) (h₁ : H.Adj x y n) :
    H.EarliestEdge x y n := by
  have h := coe_earliestEdge_of_graph_earliestEdge h₀ h₁
  exact earliestEdge_of_coe h

lemma earliestEdge_of_ge {H H' : Subgraph G} (h₀ : H ≤ H') (h₁ : H'.EarliestEdge x y n)
    (h₂ : H.Adj x y n) :
    H.EarliestEdge x y n := by
  constructor
  · trivial
  · intro _ _ h
    exact h₁.right _ _ <| h₀.right h

@[simp]
lemma coe_latestEdge {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.LatestEdge x y n) :
    H.coe.LatestEdge x y n := by
  constructor
  · exact Adj.coe h₀.left
  · intro _ _ h
    exact h₀.right _ _ h

@[simp]
lemma latestEdge_of_coe {H : Subgraph G} {x y : H.verts} {n : ℕ}
    (h₀ : H.coe.LatestEdge x y n) :
    H.LatestEdge x y n := by
  constructor
  · exact h₀.left
  · intro _ _ h
    exact h₀.right _ _ (Adj.coe h)

lemma latestEdge_of_graph_latestEdge {H : Subgraph G}
    (h₀ : G.LatestEdge x y n) (h₁ : H.Adj x y n) :
    H.LatestEdge x y n := by
  have h := coe_latestEdge_of_graph_latestEdge h₀ h₁
  exact latestEdge_of_coe h

lemma latestEdge_of_ge {H H' : Subgraph G} (h₀ : H ≤ H') (h₁ : H'.LatestEdge x y n)
    (h₂ : H.Adj x y n) :
    H.LatestEdge x y n := by
  constructor
  · trivial
  · intro _ _ h
    exact h₁.right _ _ <| h₀.right h

end EdgeProps

section NeighborHoodSet

def neighborSet (H : Subgraph G) (x : H.verts) := {y | ∃ n, H.Adj x y n}

theorem mem_neighborhoodSet (H : Subgraph G) (x : H.verts) (y : V) :
    y ∈ H.neighborSet x ↔ ∃ n, H.Adj x y n :=
  Iff.rfl

theorem neighborhoodSet_top (x : (⊤ : G.Subgraph).verts) :
    (⊤ : G.Subgraph).neighborSet x = G.neighborSet x := rfl

theorem neighborSet_subset_verts (H : Subgraph G) (x : H.verts) :
    H.neighborSet x ⊆ H.verts := by
  intro _ h
  rw [mem_neighborhoodSet] at h
  let ⟨_, h⟩ := h
  exact H.edge_vert' h

@[simp]
lemma neighborhoodSet_iff_coe {H : Subgraph G} {x : H.verts} :
    H.neighborSet x = H.coe.neighborSet x := by
  unfold neighborSet TemporalGraph.neighborSet
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

section edgeSet

-- `edgeSet` is no longer redefined here: `Subgraph` now `extends TemporalGraph V`, so
-- `H.edgeSet` resolves through generalized field notation to `TemporalGraph.edgeSet
-- H.toTemporalGraph` — the fixed, hypothesis-free definition from `Basic.lean`.

-- The `Adj → edgeSet` direction is orientation-free: it needs neither symmetry of `H` nor
-- looplessness of `G` (it is just the `Or.inl` direction of `mem_edgeSet_iff_or`).
protected theorem Adj.mem_edgeSet {H : Subgraph G} {x y : V} {n : ℕ} (h : H.Adj x y n) :
    (s(x,y), n) ∈ H.edgeSet :=
  H.mem_edgeSet_iff_or.mpr (Or.inl h)

@[simp]
lemma edgeSet_le {H : Subgraph G} {H' : Subgraph G} (h₀ : H ≤ H') :
    H.edgeSet ⊆ H'.edgeSet := by
  intro _ ⟨x, y, hp, h⟩
  exact ⟨x, y, hp, h₀.right h⟩

lemma le_iff_edgeSet_and_verts {H H' : Subgraph G} [H'.IsSymm] :
    H ≤ H' ↔ H.edgeSet ⊆ H'.edgeSet ∧ H.verts ⊆ H'.verts := by
  constructor
  · intro h
    constructor
    · apply edgeSet_le h
    · exact h.left
  · intro h
    constructor
    · exact h.right
    · intro _ _ _ hadj
      rw [←H'.mem_edgeSet]
      exact Set.mem_of_subset_of_mem h.left (Adj.mem_edgeSet hadj)

@[simp]
lemma addEdgeSymm_edgeSet (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts} :
    (H.addEdgeSymm h₀ h₁).edgeSet = insert ⟨s(x,y), n⟩ H.edgeSet := by
  ext ⟨p, n'⟩
  induction p using Sym2.ind with
  | _ a b =>
    simp only [Set.mem_insert_iff, Prod.mk.injEq, TemporalGraph.mem_edgeSet_iff_or, addEdgeSymm,
      Sym2.eq_iff]
    tauto

lemma addEdgeSymm_edgeSet' (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    (h₀ : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts) :
    (H.addEdgeSymm h₀ h₁).edgeSet = insert ⟨s(x,y), n⟩ H.edgeSet :=
  H.addEdgeSymm_edgeSet

instance {H : Subgraph G} [h : Finite H.edgeSet] {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts} :
    Finite (H.addEdgeSymm h₀ h₁).edgeSet := by
  conv =>
    rhs ; rw [H.addEdgeSymm_edgeSet, ←Set.union_singleton]
  apply Set.Finite.union
  · exact h
  · simp only [Set.finite_singleton]


@[simp]
lemma addVerts_edgeSet {H : Subgraph G} {s : Set V} :
    (H.addVerts s).edgeSet = H.edgeSet := by
  ext ⟨p, n'⟩
  constructor
  · rintro ⟨a, b, hp, _, _, hadj⟩
    exact ⟨a, b, hp, hadj⟩
  · rintro ⟨a, b, hp, hadj⟩
    exact ⟨a, b, hp, Or.inl (H.edge_vert hadj), Or.inl (H.edge_vert' hadj), hadj⟩

lemma addVerts_edgeSet' {H : Subgraph G} (s : Set V) :
    (H.addVerts s).edgeSet = H.edgeSet := addVerts_edgeSet

instance {H : Subgraph G} {s : Set V} [h₀ : Finite H.edgeSet] [Finite s] :
    Finite (H.addVerts s).edgeSet := by
  simp only [addVerts_edgeSet, h₀]

-- `edgeSet_toTemporalGraph` is gone: `H.edgeSet` now resolves through generalized field
-- notation to `H.toTemporalGraph.edgeSet` directly, making the old statement a tautology.

def footprintEdgeSet (H : Subgraph G) : Set (Sym2 V) :=
  {p | ∃ n x y, p = s(x,y) ∧ H.Adj x y n}

-- NOTE(refactor): `footprint` now returns a Mathlib `Digraph` (Basic.lean's "Relation rework"),
-- which has no `edgeSet` (directed graphs don't have unordered edges) — unlike the old
-- `SimpleGraph`-valued `footprint`. This statement can't even be typed as-is anymore; left for
-- review (likely needs restating via `footprint.Adj` or `SimpleGraph.fromRel` instead of
-- `.edgeSet`).
-- theorem FootprintEdgeSet_eq {H : Subgraph G} (hl : G.IsLoopless) :
--     H.toTemporalGraph.footprint.edgeSet = H.footprintEdgeSet := by
--   sorry

def edgeSetToFootprintEdgeSet (H : Subgraph G) : H.edgeSet → H.footprintEdgeSet :=
  fun x ↦ ⟨x.val.fst, by
    obtain ⟨a, b, hp, hadj⟩ := x.2
    exact ⟨x.val.snd, a, b, hp, hadj⟩⟩

lemma edgeSetToFootprintEdgeSet_surjective (H : Subgraph G) :
    Function.Surjective H.edgeSetToFootprintEdgeSet := by
  intro x
  obtain ⟨n, a, b, hp, hadj⟩ := x.prop
  exact ⟨⟨(x.1, n), a, b, hp, hadj⟩, rfl⟩

lemma edgeSetToFootprintEdgeSet_injective (H : Subgraph G) [H.IsSymm]
    (h₀ : H.IsSimple) :
    Function.Injective H.edgeSetToFootprintEdgeSet := by
  intro x y h
  obtain ⟨a, b, hp, hadj⟩ := x.2
  obtain ⟨a', b', hp', hadj'⟩ := y.2
  simp only [edgeSetToFootprintEdgeSet, Subtype.mk.injEq] at h
  ext
  · apply Sym2.ext_iff.mp h
  · rcases Sym2.eq_iff.mp (hp.symm.trans (h.trans hp')) with heq | heq
    · rw [heq.1.symm, heq.2.symm] at hadj'
      exact h₀ a b x.1.2 y.1.2 ⟨hadj, hadj'⟩
    · rw [heq.1.symm, heq.2.symm] at hadj'
      exact h₀ a b x.1.2 y.1.2 ⟨hadj, H.adj_symm hadj'⟩

lemma edgeSetToFootprintEdgeSet_bijective (H : Subgraph G) [H.IsSymm]
    (h₀ : H.IsSimple) :
    Function.Bijective H.edgeSetToFootprintEdgeSet :=
  ⟨H.edgeSetToFootprintEdgeSet_injective h₀, H.edgeSetToFootprintEdgeSet_surjective⟩

end edgeSet

section Size

def size (H : Subgraph G) [Fintype H.edgeSet] := Fintype.card H.edgeSet

def order (H : Subgraph G) [Fintype H.verts] := Fintype.card H.verts

lemma size_of_simple (H : Subgraph G)
    [Fintype H.edgeSet]
    [Fintype H.footprintEdgeSet]
    [H.IsSymm]
    (h₀ : H.IsSimple) :
    H.size = Fintype.card H.footprintEdgeSet := by
  apply Fintype.card_of_bijective (f := H.edgeSetToFootprintEdgeSet)
  exact H.edgeSetToFootprintEdgeSet_bijective h₀

lemma size_of_toTemporalGraph (H : Subgraph G)
    [Fintype H.edgeSet] :
    H.size = H.toTemporalGraph.size := rfl

-- NOTE(refactor): `Finite → Fintype` isn't automatic in Mathlib (avoids diamonds), so the
-- `Finite` instance above does not chain into a `Fintype` one on its own: callers must supply
-- the `Fintype` instance explicitly.
theorem addEdgeSymm_size (H : Subgraph G) {x y : V} {n : ℕ}
    [H.IsSymm] [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts}
    {h₂ : ¬H.Adj x y n}
    [Fintype H.edgeSet] [Fintype (H.addEdgeSymm h₀ h₁).edgeSet] :
    (H.addEdgeSymm h₀ h₁).size = H.size + 1 := by
  simp only [size, H.addEdgeSymm_edgeSet, H.mem_edgeSet, h₂, not_false_eq_true,
    Set.card_insert]

@[simp]
theorem addEdgeSymm_size_le (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    {h₀ : G.Adj x y n}
    {h₁ : x ∈ H.verts ∧ y ∈ H.verts}
    [Fintype H.edgeSet] [Fintype (H.addEdgeSymm h₀ h₁).edgeSet] :
    (H.addEdgeSymm h₀ h₁).size ≤ H.size + 1 := by
  unfold size
  have h : (H.addEdgeSymm h₀ h₁).edgeSet = H.edgeSet ∪ {(s(x,y), n)} := by
    simp only [H.addEdgeSymm_edgeSet, Set.union_singleton]
  have h' := Set.card_union_le H.edgeSet {(s(x,y), n)}
  simp only [h, Nat.card_eq_fintype_card, Set.card_singleton] at h' ⊢
  assumption

theorem addEdgeSymm_size_le' (H : Subgraph G) {x y : V} {n : ℕ}
    [G.IsSymm]
    (h₀ : G.Adj x y n)
    (h₁ : x ∈ H.verts ∧ y ∈ H.verts)
    [Fintype H.edgeSet] [Fintype (H.addEdgeSymm h₀ h₁).edgeSet] :
    Fintype.card (H.addEdgeSymm h₀ h₁).edgeSet ≤ Fintype.card H.edgeSet + 1 := by
  exact H.addEdgeSymm_size_le

@[simp]
theorem addVerts_size {H : Subgraph G} {s : Set V}
    [Fintype H.edgeSet]
    [Fintype (H.addVerts s).edgeSet] :
    Fintype.card (H.addVerts s).edgeSet = Fintype.card H.edgeSet := by
  simp only [addVerts_edgeSet]

end Size

end Subgraph

namespace NonemptyTemporalWalk

variable {V : Type u} {G : TemporalGraph V}

@[coe]
protected def lift_walk {H : Subgraph G} {x y : H.verts} {n m : ℕ} :
    H.coe.NonemptyTemporalWalk x n y m → G.NonemptyTemporalWalk ↑x n ↑y m
  | Single h => Single (H.adj_sub h)
  | Step p h h' =>
    Step (p.lift_walk)
      (H.adj_sub h)
      h'

instance {H : Subgraph G} {x y : H.verts} {n m : ℕ} :
    Coe (H.coe.NonemptyTemporalWalk x n y m) (G.NonemptyTemporalWalk ↑x n ↑y m) where
  coe := NonemptyTemporalWalk.lift_walk

@[coe]
protected def lift_subgraph_walk {H : Subgraph G} {H' : Subgraph G}
    {x y : H.verts}
    {n m : ℕ}
    (h : H ≤ H') :
    H.coe.NonemptyTemporalWalk x n y m → H'.coe.NonemptyTemporalWalk
      ⟨x, Set.mem_of_subset_of_mem h.left x.prop⟩ n
      ⟨y, Set.mem_of_subset_of_mem h.left y.prop⟩ m
  | Single h' => Single (h.right h')
  | Step p h' hle =>
    Step (p.lift_subgraph_walk h)
      (Subgraph.Adj.coe (h.right h'))
      hle

@[coe]
protected def lift_toTemporalGraph_walk {H : Subgraph G} {x y : H.verts} {n m : ℕ} :
    H.toTemporalGraph.NonemptyTemporalWalk x n y m → H.coe.NonemptyTemporalWalk x n y m
  | Single h => @Single H.verts H.coe x y n h
  | @Step _ _ _ y' _ _ m' _ p' h' hle' =>
      @Step H.verts H.coe x ⟨y', H.edge_vert h'⟩ y n m' m
        (p'.lift_toTemporalGraph_walk)
        h' hle'

instance {H : Subgraph G} {x y : H.verts} {n m : ℕ} :
    Coe (H.toTemporalGraph.NonemptyTemporalWalk x n y m) (H.coe.NonemptyTemporalWalk x n y m) where
  coe p := p.lift_toTemporalGraph_walk

@[coe]
protected def lift_walk_toTemporalGraph {H : Subgraph G} {x y : H.verts} {n m : ℕ} :
    H.coe.NonemptyTemporalWalk x n y m → H.toTemporalGraph.NonemptyTemporalWalk ↑x n ↑y m
  | Single h => Single h
  | Step p h h' => Step p.lift_walk_toTemporalGraph h h'

instance {H : Subgraph G} {x y : H.verts} {n m : ℕ} :
    Coe (H.coe.NonemptyTemporalWalk x n y m)
      (H.toTemporalGraph.NonemptyTemporalWalk ↑x n ↑y m) where
  coe p := p.lift_walk_toTemporalGraph

end NonemptyTemporalWalk

namespace TemporalWalk

variable {V : Type u} {G : TemporalGraph V} {H : Subgraph G}

@[coe]
protected def lift_subtempgraph_walk {x y : H.verts} {n m : ℕ} :
    H.coe.TemporalWalk x n y m → G.TemporalWalk ↑x n ↑y m
  | Empty => Empty
  | Nonempty p => Nonempty ↑p

instance {x y : H.verts} {n m : ℕ} : Coe (H.coe.TemporalWalk x n y m)
    (G.TemporalWalk ↑x n ↑y m) where
  coe := TemporalWalk.lift_subtempgraph_walk

@[coe]
protected def lift_subtempgraph_walk' {H' : Subgraph G} {x y : H.verts} {n m : ℕ}
    (h : H ≤ H') :
    H.coe.TemporalWalk x n y m → H'.coe.TemporalWalk
      ⟨x, Set.mem_of_subset_of_mem h.left x.prop⟩ n
      ⟨y, Set.mem_of_subset_of_mem h.left y.prop⟩ m
  | Empty => Empty
  | Nonempty p => Nonempty <| p.lift_subgraph_walk h

@[coe]
protected def lift_toTemporalGraph_walk {H : Subgraph G} {x y : H.verts} {n m : ℕ}
    (w : H.toTemporalGraph.TemporalWalk ↑x n ↑y m) : H.coe.TemporalWalk x n y m := by
  obtain ⟨xv, hx⟩ := x
  obtain ⟨yv, hy⟩ := y
  simp only at w ⊢
  cases w with
  | Empty =>
    exact .Empty
  | Nonempty p =>
    exact .Nonempty p.lift_toTemporalGraph_walk

instance {H : Subgraph G} {x y : H.verts} {n m : ℕ} :
    Coe (H.toTemporalGraph.TemporalWalk x n y m) (H.coe.TemporalWalk x n y m) where
  coe p := p.lift_toTemporalGraph_walk

@[coe]
protected def lift_walk_toTemporalGraph {H : Subgraph G} {x y : H.verts} {n m : ℕ} :
    H.coe.TemporalWalk x n y m → H.toTemporalGraph.TemporalWalk ↑x n ↑y m
  | Empty => Empty
  | Nonempty p => Nonempty p.lift_walk_toTemporalGraph

instance {H : Subgraph G} {x y : H.verts} {n m : ℕ} :
    Coe (H.coe.TemporalWalk x n y m) (H.toTemporalGraph.TemporalWalk ↑x n ↑y m) where
  coe p := p.lift_walk_toTemporalGraph


end TemporalWalk

section SubgraphProps

variable {V : Type u} {G : TemporalGraph V}

-- `@[simps!]` alone chokes on the `Adj` field here: it is given as the bare projection `H.Adj`
-- of an opaque parameter `H`, so simps cannot unfold it any further to a constructor application.
-- Restricting the auto-generated lemmas to `verts` and restating `Adj` by hand avoids the issue.
@[simps! verts]
def toSubgraph (H : TemporalGraph V) (h : H ≤ G) : G.Subgraph where
  verts := Set.univ
  Adj := H.Adj
  adj_sub e := h e
  edge_vert _ := Set.mem_univ _
  edge_vert' _ := Set.mem_univ _

@[simp]
theorem toSubgraph_Adj (H : TemporalGraph V) (h : H ≤ G) {x y : V} {n : ℕ} :
    (toSubgraph H h).Adj x y n ↔ H.Adj x y n :=
  Iff.rfl

theorem toSubgraph_isSpanning (H : TemporalGraph V) (h : H ≤ G) :
    (toSubgraph H h).IsSpanning :=
  Set.mem_univ

instance toSubgraph_isSymm (H : TemporalGraph V) [hs : H.IsSymm] (h : H ≤ G) :
    (toSubgraph H h).IsSymm :=
  hs

def toSubgraphTop : G.Subgraph := ⊤

-- `fromEdgeSet` lives in the `Subgraph` namespace (unlike `TemporalGraph.fromEdgeSet` in
-- `Basic.lean`, which builds a plain, symmetrized `TemporalGraph`): dot notation `G.fromEdgeSet`
-- always resolves to the `Basic.lean` one, so this constructor must be called qualified, as
-- `Subgraph.fromEdgeSet G s` — matching Mathlib's `SimpleGraph.fromEdgeSet` precedent for
-- the graph-level name.
namespace Subgraph

/-- Create a `Subgraph G` from a set of edges, the edges not in `G.edgeSet` are ignored. -/
@[simps!]
def fromEdgeSet (G : TemporalGraph V) (s : Set ((Sym2 V) × ℕ)) :
    Subgraph G where
  verts := {x | ∃ (p : s) , x ∈ p.1.1 }
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
    (fromEdgeSet G s).IsSymm := by
  constructor
  intro _ _ _ h
  simp only [fromEdgeSet, Subtype.exists, exists_and_left, exists_prop, Prod.exists, ↓existsAndEq,
    true_and] at ⊢ h
  obtain ⟨a, h⟩ := h
  use a
  simp only [h, h.2.2.2.symm, and_self]

@[simp]
theorem fromEdgeSet_eq {G : TemporalGraph V} [G.IsSymm] [G.IsLoopless]
    {s : Set ((Sym2 V) × ℕ)} (h₀ : s ⊆ G.edgeSet) :
    (fromEdgeSet G s).edgeSet = s := by
  ext ⟨p, n⟩
  constructor
  · rintro ⟨x, y, hp, a, hxa, hya, hna, hG⟩
    have heq : a.1.1 = s(x, y) := a.1.1.mem_and_mem_iff hG.ne |>.mp ⟨hxa, hya⟩
    have hpa : (p, n) = a.1 := Prod.ext (hp.trans heq.symm) hna
    rw [hpa]
    exact a.2
  · intro ha
    obtain ⟨x, y⟩ := p
    exact ⟨x, y, rfl, ⟨(s(x,y), n), ha⟩, Sym2.mem_iff.mpr (Or.inl rfl),
      Sym2.mem_iff.mpr (Or.inr rfl), rfl, G.mem_edgeSet.mp (h₀ ha)⟩

end Subgraph

end SubgraphProps

end TemporalGraph
