/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.Subgraph
import TemporalGraph.Connectivity.Subgraph

/-!
# Dismounting and mounting

This module carries out the inductive step of the spanner construction from Carnevale, Casteigts
& Corsini's revisited dismountability argument (SAND 2025, Theorem 2.1), originally due to
Casteigts, Peters & Schoeters (CPS, ICALP 2019 / JCSS): given a spanner of a clique with a vertex
removed, extend it back to a spanner of the whole clique by re-attaching that vertex through the
few edges that made it dismountable (or two-hop-dismountable) in the first place.

* `dismount` removes a single vertex from a subgraph.
* `mount` adds a vertex back with (at most) its earliest and latest edge, for the one-hop case.
* `twoHopMount` adds a vertex back reached through an intermediate vertex on each side, for the
  two-hop case (`Dismountability/Basic.lean`'s `TwoHopDismountable`).

## Main results

* `TemporalGraph.Subgraph.dismountability` : SAND 2025, Theorem 2.1 (1-hop dismountability);
  dismounting and re-mounting through the earliest and latest edge preserves being a spanner,
  adding at most 2 edges (`mount_size`).
* `TemporalGraph.Subgraph.twoHopDismountability` : SAND 2025, §2.1 (the 2-hop case, unnumbered
  in SAND); the two-hop analogue, adding at most 4 edges (`twoHopMount_size`).

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025,
  LIPIcs 330, 6:1–6:18, doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321.
* Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse Spanners*, ICALP 2019 / JCSS
  (original source of the argument).
-/

universe u
variable {V : Type u} {G : TemporalGraph V}

namespace TemporalGraph

namespace Subgraph

section Dismount

/-- Delete the vertex `x` from `H` (the "dismount" operation). -/
abbrev dismount (H : Subgraph G) (x : V) := H.deleteVerts {x}

/-- Dismounting a vertex from a clique subgraph leaves a clique subgraph. -/
lemma dismount_clique (H : Subgraph G) (x : V) (h₀ : H.IsCliqueSubgraph) :
    (H.dismount x).IsCliqueSubgraph := by
  unfold IsCliqueSubgraph IsClique dismount
  intro y hy z hz hne
  simp only [induce_verts, Set.mem_sdiff, Set.mem_singleton_iff] at hy hz
  have hy' : y ∈ H.verts := hy.1
  have hz' : z ∈ H.verts := hz.1
  have ⟨n, hadj⟩ := h₀ hy' hz' hne
  use n
  simp only [induce_Adj, Set.mem_sdiff, hy', Set.mem_singleton_iff, true_and, hz', hadj, and_true]
  exact ⟨hy.2, hz.2⟩

/-- `H.dismount x` has vertex set `H.verts \ {x}`. -/
@[simp]
lemma dismount_verts {H : Subgraph G} {x : V} : (H.dismount x).verts = H.verts \ {x} := by
  simp only [induce_verts]

/-- Dismounting a vertex yields a subgraph of the original. -/
@[simp]
lemma dismount_le {H : Subgraph G} {x : V} : (H.dismount x) ≤ H := by
  simp only [deleteVerts_le]

end Dismount

section Mount

/-- Add `x` back to `H`, connected via its earliest edge to `y` and latest edge to `z` (the
"mount" operation). -/
def mount (H : Subgraph G) [G.IsSymm] {y z : H.verts} {n m : ℕ} (x : V)
    (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    G.Subgraph :=
((H.addVerts {x}).addEdge h₀ (by simp)).addEdge h₁ (by simp)

/-- `H.mount x h₀ h₁` has vertex set `H.verts ∪ {x}`. -/
@[simp]
lemma mount_verts {H : Subgraph G} [G.IsSymm] {x : V} {y z : H.verts} {n m : ℕ}
    (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).verts = H.verts ∪ {x} := by
  rw [mount, addEdge_verts, addEdge_verts, addVerts_verts]

/-- `H.mount x h₀ h₁` is symmetric when `H` and `G` are. -/
-- `mount` is a plain `def`, so instance resolution cannot see the `addEdge`/`addVerts`
-- layers it is built from; this instance unfolds it once and hands the goal back to resolution.
instance mount_isSymm {H : Subgraph G} [H.IsSymm] [G.IsSymm] {x : V} {y z : H.verts} {n m : ℕ}
    (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).IsSymm := by
  unfold mount
  infer_instance

/-- Every vertex of `H` remains a vertex of `H.mount x h₀ h₁`. -/
@[simp]
lemma mem_mount_verts {H : Subgraph G} [G.IsSymm] {x : V} {y z : H.verts} {n m : ℕ}
    {h₀ : G.Adj y x n} {h₁ : G.Adj z x m} (x' : H.verts) :
    ↑x' ∈ (mount H x h₀ h₁).verts := by simp [mount_verts]

/-- `H.mount x h₀ h₁` contains the edge from `x` to `y` at time `n`. -/
lemma mount_edge (H : Subgraph G) [G.IsSymm] {x : V} {y z : H.verts} {n m : ℕ}
    (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).Adj x y n := by
  simp only [mount, addEdge, induce_verts, Set.union_singleton, induce_Adj,
    Set.mem_insert_iff, true_or, true_and, and_true, and_self, or_true]

/-- `H.mount x h₀ h₁` contains the edge from `z` to `x` at time `m`. -/
lemma mount_edge' (H : Subgraph G) [G.IsSymm] {x : V} {y z : H.verts} {n m : ℕ}
    (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H x h₀ h₁).Adj z x m := by
  rw [mount]
  apply addEdge_edge

/-- `H` is a subgraph of `H.mount x h₀ h₁`. -/
lemma mount_le {H : Subgraph G} [G.IsSymm] {x : V} {y z : H.verts} {n m : ℕ}
    {h₀ : G.Adj y x n} {h₁ : G.Adj z x m} :
    H ≤ H.mount x h₀ h₁ := by
  unfold mount
  have h := addVerts_le' H {x}
  have h' := h.trans <| addEdge_le' (H.addVerts {x}) h₀ (by simp)
  exact le_trans h' addEdge_le

/-- `H.mount x h₀ h₁` has edge set `H.edgeSet` plus the two new edges `z x` at `m` and `y x` at
`n`. -/
@[simp]
lemma mount_edgeSet (H : Subgraph G) [G.IsSymm] [G.IsLoopless] {x : V} {y z : H.verts} {n m : ℕ}
    (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (H.mount x h₀ h₁).edgeSet = H.edgeSet ∪ {⟨s(z,x), m⟩, ⟨s(y,x), n⟩} := by
  simp [mount, addEdge_edgeSet, addVerts_edgeSet]

/-- If dismounting `x` from `H` (via its earliest edge to `y` and latest edge to `z`) is
temporally connected, so is `H.mount x h₀ h₁`, provided those edges are indeed the earliest and
latest edges at `x`. -/
theorem mount_tc (H : Subgraph G) [H.IsSymm] [G.IsSymm] {x : V} {y z : H.verts} {n m : ℕ}
    (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) (h₂ : (mount H x h₀ h₁).EarliestEdge y x n)
    (h₃ : (mount H x h₀ h₁).LatestEdge z x m) :
    H.TemporallyConnected → (mount H x h₀ h₁).TemporallyConnected := by
  have hReach : ∀ x' y', H.Reachable x' y' → (mount H x h₀ h₁).Reachable
    ⟨x', by simp [mount_verts]⟩
    ⟨y', by simp [mount_verts]⟩
    := reachable_of_le_reachable mount_le
  unfold Subgraph.TemporallyConnected
  intro hTC
  have hy : y.val ∈ (mount H x h₀ h₁).verts := by simp [mount_verts]
  have hx : x ∈ (mount H x h₀ h₁).verts := by simp [mount_verts]
  have hz : z.val ∈ (mount H x h₀ h₁).verts := by simp [mount_verts]
  simp only [Reachable, Subtype.forall, mount_verts, Set.union_singleton, Set.mem_insert_iff]
  intro x' hx' y' hy'
  apply hx'.elim
  · intro heq ; apply hy'.elim
    <;> conv => rhs ; lhs ; lhs ; rw [heq]
    · intro heq'
      -- `reachable_of_self` is `@[refl]`, so the `rfl` that `rw` attempts already closes this.
      conv => rhs ; lhs ; rw [heq']
    · intro hy'₀
      have hy'₁ : y' ∈ (mount H x h₀ h₁).verts := by simp [hy']
      apply @reachable_of_earliestEdge _ _ (mount H x h₀ h₁) ⟨y, _⟩ ⟨x, _⟩ n inferInstance h₂
        ⟨y', _⟩
      exact hReach ⟨y, _⟩ ⟨y', hy'₀⟩ <| hTC _ _
  · intro hx' ; apply hy'.elim
    · intro heq
      conv => rhs ; lhs ; rw [heq]
      apply @reachable_of_latestEdge _ _ (mount H x h₀ h₁) ⟨z, _⟩ ⟨x, _⟩ m inferInstance h₃
        ⟨x', _⟩
      exact hReach ⟨x', hx'⟩ ⟨z, _⟩ <| hTC _ _
    · intro hy' ; exact hReach ⟨x', hx'⟩ ⟨y', hy'⟩ <| hTC _ _

instance {H : Subgraph G} [h₀ : Finite H.edgeSet] [G.IsSymm] [G.IsLoopless] {x : V}
    {y z : H.verts} {n m : ℕ} {h₁ : G.Adj y x n} {h₂ : G.Adj z x m} :
    Finite (H.mount x h₁ h₂).edgeSet := by
  conv =>
    rhs ; rw [H.mount_edgeSet]
  apply Set.Finite.union
  · trivial
  · simp only [Set.finite_insert, Set.finite_singleton]

/-- Mounting `x` back onto `H` adds at most 2 edges. -/
theorem mount_size {H : Subgraph G} [Fintype H.edgeSet] [G.IsSymm] [G.IsLoopless] {x : V}
    {y z : H.verts} {n m : ℕ} {h₀ : G.Adj y x n} {h₁ : G.Adj z x m}
    [Fintype (H.mount x h₀ h₁).edgeSet] :
    Fintype.card (H.mount x h₀ h₁).edgeSet ≤ Fintype.card H.edgeSet + 2 := by
  -- Rewrite the edge set only once under `Nat.card`: under `Fintype.card` it clashes with the
  -- `Fintype` instance that depends on it.
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, H.mount_edgeSet]
  have hle₀ : Nat.card ({(s(↑z, x), m), (s(↑y, x), n)} : Set ((Sym2 V) × ℕ)) ≤ 2 := by
    simp only [←Set.union_singleton]
    have h : 2 = 1 + 1 := by simp only [Nat.reduceAdd]
    have h' : Fintype.card ({(s(↑z, x), m)} : Set (Sym2 V × ℕ)) = 1 := by simp
    have h'' : Fintype.card ({(s(↑y, x), n)} : Set (Sym2 V × ℕ)) = 1 := by simp
    conv => rhs ; rw [h] ; arg 1 ; rw [←h'']
    conv => arg 2 ; arg 2 ; rw [←h']
    simp only [←Nat.card_eq_fintype_card, Set.card_union_le]
  have hle₁ : Nat.card ↑(H.edgeSet ∪ {(s(↑z, x), m), (s(↑y, x), n)})
      ≤ Nat.card H.edgeSet + Nat.card ({(s(↑z, x), m), (s(↑y, x), n)} : Set ((Sym2 V) × ℕ)) := by
    simp only [Set.card_union_le]
  lia

/-- SAND 2025, Theorem 2.1 (1-hop case): re-mounting `x` via its earliest edge to `y` and latest
edge to `z` extends a spanner of `H.dismount x` to a spanner of `H`, when `H` is a clique. -/
theorem dismountability {H H' : Subgraph G} [H.IsSymm] [H'.IsSymm] [G.IsSymm] [G.IsLoopless]
    {x : H.verts} {y z : H'.verts} {n m : ℕ}
    (h₀ : H.IsCliqueSubgraph) (h₁ : G.Adj y x n) (h₂ : G.Adj z x m) (h₃ : H.EarliestEdge y x n)
    (h₄ : H.LatestEdge z x m) (h₅ : H'.IsSpannerOf (H.dismount x)) :
    H'.mount x h₁ h₂ |>.IsSpannerOf H := by
  have heq : (H'.mount x h₁ h₂).verts = H.verts := by simp only [mount_verts, h₅.right.choose,
    induce_verts, Set.union_singleton, Subtype.coe_prop, Set.insert_sdiff_self_of_mem]
  have hle : H'.mount x h₁ h₂ ≤ H := by
    apply le_iff_edgeSet_and_verts.mpr
    constructor
    · rw [H'.mount_edgeSet]
      have hsplit : H.edgeSet = H.edgeSet ∪ H.edgeSet := by simp
      rw [hsplit]
      apply Set.union_subset_union
      · apply edgeSet_le
        apply le_trans h₅.left dismount_le
      · have : (s(↑z, ↑x), m) ∈ H.edgeSet := by
          rw [H.mem_edgeSet]
          apply h₄.left
        have : (s(↑y, ↑x), n) ∈ H.edgeSet := by
          rw [H.mem_edgeSet]
          apply h₃.left
        grind
    · simp only [mount_verts, h₅.right.choose, induce_verts, Set.union_singleton, Subtype.coe_prop,
      Set.insert_sdiff_self_of_mem, subset_refl]
  have htc : (H'.mount x h₁ h₂).TemporallyConnected := by
    apply mount_tc H'
    · apply earliestEdge_of_ge _ h₃
      · exact (mount_edge H' h₁ h₂).symm
      · trivial
    · apply latestEdge_of_ge _ h₄
      · apply mount_edge'
      · trivial
    · have htc : (H.dismount x).IsCliqueSubgraph := by
        apply dismount_clique
        exact h₀
      rw [isClique_iff_coe] at htc
      apply temporallyConnected_of_isClique at htc
      rw [←temporallyConnected_iff] at htc
      unfold TemporallyConnected at htc ⊢
      intro u v
      have := htc ⟨u, by grind only [h₅.right.choose]⟩ ⟨v, by grind only [h₅.right.choose]⟩
      obtain ⟨_, h⟩ := h₅.right
      exact h _ _ this
  constructor
  · trivial
  · use heq
    intro u v _
    simpa using htc ⟨u, by grind only⟩ ⟨v, by grind only⟩

end Mount

section TwoHopMount

/-- Add `x` back to `H`, connected through `y'` on the earliest side and `z'` on the latest side
(the two-hop "mount" operation). -/
def twoHopMount (H : Subgraph G) [G.IsSymm] {y y' z z' : H.verts} {n n' m m' : ℕ} (x : V)
    (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m') (h₃ : G.Adj z' z m) :
    G.Subgraph :=
  H.addVerts {x}
    |>.addEdge h₀ (by simp)
    |>.addEdge h₁ (by simp)
    |>.addEdge h₂ (by simp)
    |>.addEdge h₃ (by simp)

/-- `H.twoHopMount x h₀ h₁ h₂ h₃` has vertex set `H.verts ∪ {x}`. -/
@[simp]
lemma twoHopMount_verts (H : Subgraph G) [G.IsSymm] {y y' z z' : H.verts} {n n' m m' : ℕ} (x : V)
    (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m') (h₃ : G.Adj z' z m) :
    (H.twoHopMount x h₀ h₁ h₂ h₃).verts = H.verts ∪ {x} := by
  simp only [twoHopMount, addEdge_verts, induce_verts, Set.union_singleton]

/-- `H.twoHopMount x h₀ h₁ h₂ h₃` is symmetric when `H` and `G` are. -/
-- Same as `mount_isSymm`: resolution stops at the `def`, so unfold the four `addEdge`
-- layers once and let the `addEdge_isSymm`/`addVerts_isSymm` instances take over.
instance twoHopMount_isSymm (H : Subgraph G) [H.IsSymm] [G.IsSymm] {y y' z z' : H.verts}
    {n n' m m' : ℕ} (x : V) (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.twoHopMount x h₀ h₁ h₂ h₃).IsSymm := by
  unfold twoHopMount
  infer_instance

/-- Every vertex of `H` remains a vertex of `H.twoHopMount x h₀ h₁ h₂ h₃`. -/
@[simp]
lemma mem_twoHopMount_verts {H : Subgraph G} [G.IsSymm] {y y' z z' : H.verts} {n n' m m' : ℕ}
    {x : V} {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m}
    (x' : H.verts) :
    ↑x' ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).verts := by
  simp [twoHopMount_verts]

/-- `H.twoHopMount x h₀ h₁ h₂ h₃` has edge set `H.edgeSet` plus the four new edges. -/
@[simp]
lemma twoHopMount_edgeSet (H : Subgraph G) [G.IsSymm] [G.IsLoopless] {y y' z z' : H.verts}
    {n n' m m' : ℕ} (x : V) (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.twoHopMount x h₀ h₁ h₂ h₃).edgeSet =
    H.edgeSet ∪ {⟨s(z', z), m⟩,  ⟨s(x, z'), m'⟩, ⟨s(y',y), n⟩, ⟨s(x,y'), n'⟩} := by
  simp [twoHopMount, addEdge_edgeSet, addVerts_edgeSet]

/-- `H.twoHopMount x h₀ h₁ h₂ h₃` contains the edge from `x` to `y'` at time `n'`. -/
-- The four edges below are the ones `twoHopMount` inserts directly, so each is obtained by
-- lifting `addEdge_edge` along the later `addEdge_le` layers: no symmetry needed.
lemma twoHopMount_edge {H : Subgraph G} [G.IsSymm] {y y' z z' : H.verts} {n n' m m' : ℕ} {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount x h₀ h₁ h₂ h₃).Adj x y' n' := by
  rw [twoHopMount]
  exact addEdge_le.right <| addEdge_le.right <| addEdge_le.right addEdge_edge

/-- `H.twoHopMount x h₀ h₁ h₂ h₃` contains the edge from `x` to `z'` at time `m'`. -/
lemma twoHopMount_edge' {H : Subgraph G} [G.IsSymm] {y y' z z' : H.verts} {n n' m m' : ℕ} {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount x h₀ h₁ h₂ h₃).Adj x z' m' := by
  rw [twoHopMount]
  exact addEdge_le.right addEdge_edge

/-- `H.twoHopMount x h₀ h₁ h₂ h₃` contains the edge from `y'` to `y` at time `n`. -/
lemma twoHopMount_edge'' {H : Subgraph G} [G.IsSymm] {y y' z z' : H.verts} {n n' m m' : ℕ} {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount x h₀ h₁ h₂ h₃).Adj y' y n := by
  rw [twoHopMount]
  exact addEdge_le.right <| addEdge_le.right addEdge_edge

/-- `H.twoHopMount x h₀ h₁ h₂ h₃` contains the edge from `z'` to `z` at time `m`. -/
lemma twoHopMount_edge''' {H : Subgraph G} [G.IsSymm] {y y' z z' : H.verts} {n n' m m' : ℕ} {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount x h₀ h₁ h₂ h₃).Adj z' z m := by
  rw [twoHopMount]
  exact addEdge_edge

/-- `H` is a subgraph of `H.twoHopMount x h₀ h₁ h₂ h₃`. -/
@[simp]
lemma twoHopMount_le {H : Subgraph G} [G.IsSymm] {y y' z z' : H.verts} {n n' m m' : ℕ} {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    H ≤ H.twoHopMount x h₀ h₁ h₂ h₃ :=
  addVerts_le' H {x}
    |>.trans (addEdge_le' _ h₀ (by simp))
    |>.trans (addEdge_le' _ h₁ (by simp))
    |>.trans (addEdge_le' _ h₂ (by simp))
    |>.trans (addEdge_le' _ h₃ (by simp))

/-- If dismounting `x` (via `y'`, `y` on the earliest side and `z'`, `z` on the latest side) is
temporally connected, so is `H.twoHopMount x h₀ h₁ h₂ h₃`. -/
theorem twoHopMount_TC (H : Subgraph G) [H.IsSymm] [G.IsSymm] {y y' z z' : H.verts}
    {n n' m m' : ℕ} (x : V) (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) (h₄ : (H.twoHopMount x h₀ h₁ h₂ h₃).EarliestEdge y y' n ∧ n' ≤ n)
    (h₅ : (H.twoHopMount x h₀ h₁ h₂ h₃).LatestEdge z z' m ∧ m ≤ m') :
    H.TemporallyConnected → (H.twoHopMount x h₀ h₁ h₂ h₃).TemporallyConnected := by
  have hReach : ∀ x' y', H.Reachable x' y' → (twoHopMount H x h₀ h₁ h₂ h₃).Reachable
    ⟨x', by simp [twoHopMount_verts]⟩
    ⟨y', by simp [twoHopMount_verts]⟩
    := reachable_of_le_reachable twoHopMount_le
  intro htc
  have hx  : x ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).verts   := by simp
  have hy  : ↑y ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).verts  := by simp
  have hy' : ↑y' ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).verts := by simp
  have hz  : ↑z ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).verts  := by simp
  have hz' : ↑z' ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).verts := by simp
  simp only [TemporallyConnected, Reachable, Subtype.forall, twoHopMount_verts, Set.union_singleton,
    Set.mem_insert_iff]
  intro a ha b hb
  apply Or.elim ha
  · intro heq
    apply Or.elim hb
    · intro heq'
      simp only [heq, heq', reachable_of_self]
    · intro hb
      simp only [heq]
      have hb' : ↑b ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).verts := mem_twoHopMount_verts ⟨b, hb⟩
      apply @reachable_of_extended_earliestEdge _ _ (H.twoHopMount x h₀ h₁ h₂ h₃)
        ⟨y, hy⟩ ⟨y', hy'⟩ ⟨x, hx⟩ _ _ inferInstance h₄.left twoHopMount_edge
        h₄.right ⟨b, hb'⟩
      apply hReach y ⟨b, hb⟩
      apply htc
  · intro ha
    apply Or.elim hb
    · intro heq
      simp only [heq]
      have ha' : ↑a ∈ (H.twoHopMount x h₀ h₁ h₂ h₃).verts := mem_twoHopMount_verts ⟨a, ha⟩
      apply @reachable_of_extended_latestEdge _ _ (H.twoHopMount x h₀ h₁ h₂ h₃)
        ⟨z, hz⟩ ⟨z', hz'⟩ ⟨x, hx⟩ _ _ inferInstance h₅.left
        twoHopMount_edge'.symm h₅.right ⟨a, ha'⟩
      apply hReach ⟨a, ha⟩ z
      apply htc
    · intro hb
      apply hReach ⟨a, ha⟩ ⟨b, hb⟩
      apply htc

instance {H : Subgraph G} [h₀ : Finite H.edgeSet] [G.IsSymm] [G.IsLoopless] {y y' z z' : H.verts}
    {n n' m m' : ℕ} {x : V} {h₁ : G.Adj x y' n'} {h₂ : G.Adj y' y n} {h₃ : G.Adj x z' m'}
    {h₄ : G.Adj z' z m} :
    Finite (H.twoHopMount x h₁ h₂ h₃ h₄).edgeSet := by
  conv =>
    rhs ; rw [H.twoHopMount_edgeSet x h₁ h₂ h₃ h₄]
  apply Set.Finite.union
  · trivial
  · simp only [Set.finite_insert, Set.finite_singleton]

/-- Mounting `x` back onto `H` via two hops on each side adds at most 4 edges. -/
theorem twoHopMount_size {H : Subgraph G} [Fintype H.edgeSet] [G.IsSymm] [G.IsLoopless]
    {y y' z z' : H.verts} {n n' m m' : ℕ} {x : V} {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n}
    {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} [Fintype (H.twoHopMount x h₀ h₁ h₂ h₃).edgeSet] :
    Fintype.card (H.twoHopMount x h₀ h₁ h₂ h₃).edgeSet ≤ Fintype.card H.edgeSet + 4 := by
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, H.twoHopMount_edgeSet x h₀ h₁ h₂ h₃]
  have hle₀ :
      Nat.card ({(s(↑z', ↑z), m), (s(x, ↑z'), m'),
      (s(↑y', ↑y), n), (s(x, ↑y'), n')} : Set ((Sym2 V) × ℕ)) ≤ 4 := by
    have h :  4 = 1 + 1 + 1 + 1 := by simp only [Nat.reduceAdd]
    have heq₀ : Nat.card ({(s(↑z', ↑z), m)} : Set (Sym2 V × ℕ)) = 1 := by simp
    have heq₁ : Nat.card ({(s(x, z'), m')} : Set (Sym2 V × ℕ)) = 1 := by simp
    have heq₂ : Nat.card ({(s(↑y', ↑y), n)} : Set (Sym2 V × ℕ)) = 1 := by simp
    have heq₃ : Nat.card ({(s(x, ↑y'), n')} : Set (Sym2 V × ℕ)) = 1 := by simp
    grind only [Set.card_union_le, !Set.insert_eq]
  have hle₁ :
      Nat.card ↑(H.edgeSet ∪ {⟨s(z', z), m⟩,  ⟨s(x, z'), m'⟩, ⟨s(y',y), n⟩, ⟨s(x,y'), n'⟩})
      ≤ Nat.card H.edgeSet  + Nat.card ({(s(↑z', ↑z), m), (s(x, ↑z'), m'), (s(↑y', ↑y), n),
        (s(x, ↑y'), n')} : Set ((Sym2 V) × ℕ)) := by
    simp only [Set.card_union_le]
  lia

/-- SAND 2025, §2.1 (2-hop case): re-mounting `x` via two hops on each side extends a spanner of
`H.dismount x` to a spanner of `H`, when `H` is a clique. -/
theorem twoHopDismountability {H H' : Subgraph G} [H.IsSymm] [H'.IsSymm] [G.IsSymm] [G.IsLoopless]
    {x : H.verts} {y y' z z' : H'.verts} {n n' m m' : ℕ}
    (h₀ : H.IsCliqueSubgraph) (h₁ : G.Adj x y' n') (h₂ : G.Adj y' y n) (h₃ : G.Adj x z' m')
    (h₄ : G.Adj z' z m) (h₅ : H.EarliestEdge y y' n ∧ n' ≤ n ∧ H.Adj x y' n')
    (h₆ : H.LatestEdge z z' m ∧ m ≤ m' ∧ H.Adj x z' m') (h₇ : H'.IsSpannerOf (H.dismount x)) :
    H'.twoHopMount x h₁ h₂ h₃ h₄ |>.IsSpannerOf H := by
  have heq : (H'.twoHopMount x h₁ h₂ h₃ h₄).verts = H.verts := by
    simp [twoHopMount_verts, h₇.right.choose]
  have hle : (H'.twoHopMount x h₁ h₂ h₃ h₄) ≤ H := by
    apply le_iff_edgeSet_and_verts.mpr
    constructor
    · rw [H'.twoHopMount_edgeSet x h₁ h₂ h₃ h₄]
      have hsplit : H.edgeSet = H.edgeSet ∪ H.edgeSet := by simp
      rw [hsplit]
      apply Set.union_subset_union
      · apply edgeSet_le
        apply le_trans h₇.left dismount_le
      · have : (s(↑z, ↑z'), m) ∈ H.edgeSet := by
          rw [H.mem_edgeSet]
          apply h₆.1.1
        have : (s(↑x, ↑z'), m') ∈ H.edgeSet := by
          rw [H.mem_edgeSet]
          apply h₆.2.2
        have : (s(↑y, ↑y'), n) ∈ H.edgeSet := by
          rw [H.mem_edgeSet]
          apply h₅.1.1
        have : (s(↑x, ↑y'), n') ∈ H.edgeSet := by
          rw [H.mem_edgeSet]
          apply h₅.2.2
        grind
    · exact heq.le
  have htc : (H'.twoHopMount x h₁ h₂ h₃ h₄).TemporallyConnected := by
    apply twoHopMount_TC H' ↑x
    · apply And.intro
      · apply earliestEdge_of_ge _ h₅.left
        · exact twoHopMount_edge''.symm
        · trivial
      · exact h₅.2.1
    · apply And.intro
      · apply latestEdge_of_ge _ h₆.left
        · exact twoHopMount_edge'''.symm
        · trivial
      · exact h₆.2.1
    · have hclique : (H.dismount x).IsCliqueSubgraph := by
        apply dismount_clique
        exact h₀
      rw [isClique_iff_coe] at hclique
      apply temporallyConnected_of_isClique at hclique
      rw [←temporallyConnected_iff] at hclique
      unfold TemporallyConnected at hclique ⊢
      intro u v
      have := hclique ⟨u, by grind only [h₇.right.choose]⟩ ⟨v, by grind only [h₇.right.choose]⟩
      obtain ⟨_, h⟩ := h₇.right
      exact h _ _ this
  constructor
  · trivial
  · use heq
    intro u v _
    simpa using htc ⟨u, by grind only⟩ ⟨v, by grind only⟩

end TwoHopMount

end Subgraph

end TemporalGraph
