/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Basic
public import TemporalGraph.Subgraph
public import TemporalGraph.Connectivity.Subgraph
public import TemporalGraph.Dismountability.Basic

import TemporalGraph.Helpers.SetCard

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
  adding at most 2 edges (`mount_size`, `ncard_edgeSet_mount_le`).
* `TemporalGraph.Subgraph.twoHopDismountability` : SAND 2025, §2.1 (the 2-hop case, unnumbered
  in SAND); the two-hop analogue, adding at most 4 edges (`twoHopMount_size`,
  `ncard_edgeSet_twoHopMount_le`).
* `TemporalGraph.Subgraph.exists_edgeSet_of_earliest`, `exists_edgeSet_of_latest` : the two sides
  of `{1,2}`-hop dismountability, as a set of at most two edges of `H`.
* `TemporalGraph.Subgraph.exists_isSpannerOf_of_twoHopDismountable` : SAND 2025, Theorem 2.1
  and §2.1, a `{1,2}`-hop dismountable clique has a vertex `x` such that every spanner of
  `H.dismount x` extends to a spanner of `H` with at most 4 more edges. The witness on each side
  (earliest, latest) is a set of 1 or 2 edges, so the mixed 1/2-hop cases are handled at once.
  This is the form used by the induction below; `dismountability` and `twoHopDismountability`
  are the paper-faithful statements, with explicit `mount`s.
* `TemporalGraph.Subgraph.exists_isSpannerOf_ncard_le_of_forall_not_twoHopDismountable` :
  the generic induction on cliques, the central entry point of the library: if every finite simple
  proper clique that is not `{1,2}`-hop dismountable has a spanner with at most `f n` edges and
  `f n + 4 ≤ f (n + 1)`, then every finite simple proper clique has one. The `O(n log n)` and
  `7n` bounds are instances.

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025,
  LIPIcs 330, 6:1–6:18, doi:10.4230/LIPIcs.SAND.2025.6, arXiv:2502.01321.
* Casteigts, Peters & Schoeters, *Temporal Cliques Admit Sparse Spanners*, ICALP 2019 / JCSS
  (original source of the argument).
-/

@[expose] public section

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
@[simp, grind =]
lemma dismount_verts {H : Subgraph G} {x : V} : (H.dismount x).verts = H.verts \ {x} := by
  simp only [induce_verts]

/-- Dismounting a vertex yields a subgraph of the original. -/
@[simp]
lemma dismount_le {H : Subgraph G} {x : V} : (H.dismount x) ≤ H := by
  simp only [deleteVerts_le]

/-- A spanner `H'` of the dismount `H.dismount x` of a clique `H` is temporally connected: the
dismount is a clique, hence temporally connected, and the spanner preserves that. -/
private lemma temporallyConnectedSubgraph_of_isSpannerOf_dismount {H H' : Subgraph G} {x : V}
    (h₀ : H.IsCliqueSubgraph) (h₁ : H'.IsSpannerOf (H.dismount x)) :
    H'.TemporallyConnectedSubgraph := by
  have hdisTC : (H.dismount x).TemporallyConnectedSubgraph :=
    TemporalGraph.temporallyConnected_of_isClique _ (dismount_clique H x h₀)
  intro u hu v hv
  rw [h₁.right.1] at hu hv
  exact h₁.right.right u hu v hv (hdisTC u hu v hv)

end Dismount

section Mount

/-- Add `x` back to `H`, connected via its earliest edge to `y` and latest edge to `z` (the
"mount" operation). -/
def mount (H : Subgraph G) [G.IsSymm] {y z : V} {n m : ℕ} (hy : y ∈ H.verts) (hz : z ∈ H.verts)
    (x : V) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    G.Subgraph :=
  ((H.addVerts {x}).addEdge h₀ (by simp [hy])).addEdge h₁ (by simp [hz])

/-- `H.mount hy hz x h₀ h₁` has vertex set `H.verts ∪ {x}`. -/
@[simp, grind =]
lemma mount_verts {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H hy hz x h₀ h₁).verts = H.verts ∪ {x} := by
  rw [mount, addEdge_verts, addEdge_verts, addVerts_verts]

/-- `H.mount hy hz x h₀ h₁` is symmetric when `H` and `G` are. As `mount` is a plain `def`,
instance resolution cannot see the `addEdge`/`addVerts` layers it is built from; this instance
unfolds it once and hands the goal back to resolution. -/
instance mount_isSymm {H : Subgraph G} [H.IsSymm] [G.IsSymm] {x y z : V} {n m : ℕ}
    (hy : y ∈ H.verts) (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H hy hz x h₀ h₁).IsSymm := by
  unfold mount
  infer_instance

/-- Every vertex of `H` remains a vertex of `H.mount hy hz x h₀ h₁`. -/
@[simp]
lemma mem_mount_verts {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ} {hy : y ∈ H.verts}
    {hz : z ∈ H.verts} {h₀ : G.Adj y x n} {h₁ : G.Adj z x m} {x' : V} (hx' : x' ∈ H.verts) :
    x' ∈ (mount H hy hz x h₀ h₁).verts := by simp [mount_verts, hx']

/-- `H.mount hy hz x h₀ h₁` contains the edge from `x` to `y` at time `n`. -/
lemma mount_adj_left (H : Subgraph G) [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H hy hz x h₀ h₁).Adj x y n := by
  simp only [mount, addEdge, induce_verts, Set.union_singleton, induce_Adj,
    Set.mem_insert_iff, true_or, true_and, and_true, and_self, or_true]

/-- `H.mount hy hz x h₀ h₁` contains the edge from `z` to `x` at time `m`. -/
lemma mount_adj_right (H : Subgraph G) [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H hy hz x h₀ h₁).Adj z x m := by
  rw [mount]
  apply addEdge_edge

/-- `H` is a subgraph of `H.mount hy hz x h₀ h₁`. -/
lemma mount_le {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) {h₀ : G.Adj y x n} {h₁ : G.Adj z x m} :
    H ≤ H.mount hy hz x h₀ h₁ := by
  unfold mount
  have h := addVerts_le (H := H) (s := {x})
  have h' := h.trans <| addEdge_le (h := h₀) (h₁ := by simp [hy])
  exact le_trans h' addEdge_le

/-- `H.mount hy hz x h₀ h₁` has edge set `H.edgeSet` plus the two new edges `z x` at `m` and `y x`
at `n`. -/
@[simp]
lemma mount_edgeSet (H : Subgraph G) [G.IsSymm] {x y z : V} {n m : ℕ}
    (hy : y ∈ H.verts) (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (H.mount hy hz x h₀ h₁).edgeSet = H.edgeSet ∪ {⟨s(z, x), m⟩, ⟨s(y, x), n⟩} := by
  simp [mount, addEdge_edgeSet, addVerts_edgeSet]

/-- If dismounting `x` from `H` (via its earliest edge to `y` and latest edge to `z`) is
temporally connected, so is `H.mount hy hz x h₀ h₁`, provided those edges are indeed the earliest
and latest edges at `x`. -/
theorem mount_temporallyConnected (H : Subgraph G) [H.IsSymm] [G.IsSymm] {x y z : V} {n m : ℕ}
    (hy : y ∈ H.verts) (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m)
    (h₂ : (mount H hy hz x h₀ h₁).EarliestEdge y x n)
    (h₃ : (mount H hy hz x h₀ h₁).LatestEdge z x m) :
    H.TemporallyConnectedSubgraph → (mount H hy hz x h₀ h₁).TemporallyConnectedSubgraph := by
  intro hTC
  have hReach : ∀ a b : V, H.Reachable a b → (mount H hy hz x h₀ h₁).Reachable a b :=
    fun _ _ ↦ reachable_mono (mount_le hy hz)
  intro a ha b hb
  simp only [mount_verts, Set.union_singleton, Set.mem_insert_iff] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact Reachable.refl _
    · exact reachable_of_earliestEdge h₂ b (hReach y b (hTC y hy b hb))
  · rcases hb with rfl | hb
    · exact reachable_of_latestEdge h₃ a (hReach a z (hTC a ha z hz))
    · exact hReach a b (hTC a ha b hb)

instance finite_edgeSet_mount {H : Subgraph G} [h₀ : Finite H.edgeSet] [G.IsSymm] {x y z : V}
    {n m : ℕ} {hy : y ∈ H.verts} {hz : z ∈ H.verts} {h₁ : G.Adj y x n} {h₂ : G.Adj z x m} :
    Finite (H.mount hy hz x h₁ h₂).edgeSet := by
  rw [H.mount_edgeSet]
  infer_instance

/-- Instance-free form of `mount_size`: mounting `x` back onto `H` adds at most 2 edges to
`H.edgeSet`'s `Set.ncard`. -/
theorem ncard_edgeSet_mount_le {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ}
    {hy : y ∈ H.verts} {hz : z ∈ H.verts} {h₀ : G.Adj y x n} {h₁ : G.Adj z x m} :
    (H.mount hy hz x h₀ h₁).edgeSet.ncard ≤ H.edgeSet.ncard + 2 := by
  rw [H.mount_edgeSet]
  have hunion := Set.ncard_union_le H.edgeSet ({⟨s(z, x), m⟩, ⟨s(y, x), n⟩} : Set (Sym2 V × ℕ))
  have hpair := Set.ncard_pair_le (⟨s(z, x), m⟩ : Sym2 V × ℕ) ⟨s(y, x), n⟩
  -- `|E ∪ {e₁, e₂}| ≤ |E| + |{e₁, e₂}| ≤ |E| + 2`
  omega

/-- Mounting `x` back onto `H` adds at most 2 edges. -/
theorem mount_size {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ}
    {hy : y ∈ H.verts} {hz : z ∈ H.verts} {h₀ : G.Adj y x n} {h₁ : G.Adj z x m}
    [Fintype H.edgeSet] [Fintype (H.mount hy hz x h₀ h₁).edgeSet] :
    (H.mount hy hz x h₀ h₁).size ≤ H.size + 2 := by
  rw [size_eq_ncard, size_eq_ncard]
  exact ncard_edgeSet_mount_le

/-- SAND 2025, Theorem 2.1 (1-hop case): re-mounting `x` via its earliest edge to `y` and latest
edge to `z` extends a spanner of `H.dismount x` to a spanner of `H`, when `H` is a clique. -/
theorem dismountability {H H' : Subgraph G} [H.IsSymm] [H'.IsSymm] [G.IsSymm]
    {x y z : V} {n m : ℕ} (hx : x ∈ H.verts) (hy : y ∈ H'.verts) (hz : z ∈ H'.verts)
    (h₀ : H.IsCliqueSubgraph) (h₁ : G.Adj y x n) (h₂ : G.Adj z x m) (h₃ : H.EarliestEdge y x n)
    (h₄ : H.LatestEdge z x m) (h₅ : H'.IsSpannerOf (H.dismount x)) :
    (H'.mount hy hz x h₁ h₂).IsSpannerOf H := by
  have heq : (H'.mount hy hz x h₁ h₂).verts = H.verts := by simp only [mount_verts, h₅.right.1,
    induce_verts, Set.union_singleton, hx, Set.insert_sdiff_self_of_mem]
  have hle : H'.mount hy hz x h₁ h₂ ≤ H := by
    apply le_iff_edgeSet_and_verts.mpr
    constructor
    · rw [H'.mount_edgeSet]
      refine Set.union_subset (edgeSet_mono (h₅.left.trans dismount_le)) ?_
      -- the two edges added by the mount are edges of `H`
      have : (s(z, x), m) ∈ H.edgeSet := H.mem_edgeSet.mpr h₄.left
      have : (s(y, x), n) ∈ H.edgeSet := H.mem_edgeSet.mpr h₃.left
      grind only [= Sym2.eq, = Set.subset_def, = Set.mem_insert_iff, = Set.mem_singleton_iff]
    · simp only [mount_verts, h₅.right.1, induce_verts, Set.union_singleton, hx,
      Set.insert_sdiff_self_of_mem, subset_refl]
  -- the mount is temporally connected, hence a spanner of the clique `H`
  have htc : (H'.mount hy hz x h₁ h₂).TemporallyConnectedSubgraph := by
    apply mount_temporallyConnected H'
    · exact earliestEdge_of_le hle h₃ (mount_adj_left H' hy hz h₁ h₂).symm
    · exact latestEdge_of_le hle h₄ (mount_adj_right H' hy hz h₁ h₂)
    · exact temporallyConnectedSubgraph_of_isSpannerOf_dismount h₀ h₅
  refine ⟨hle, heq, fun u hu v hv _ ↦ htc u ?_ v ?_⟩
  · rwa [heq]
  · rwa [heq]

end Mount

section TwoHopMount

/-- Add `x` back to `H`, connected through `y'` on the earliest side and `z'` on the latest side
(the two-hop "mount" operation). -/
def twoHopMount (H : Subgraph G) [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ} (hy : y ∈ H.verts)
    (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) (x : V)
    (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m') (h₃ : G.Adj z' z m) :
    G.Subgraph :=
  H.addVerts {x}
    |>.addEdge h₀ (by simp [hy'])
    |>.addEdge h₁ (by simp [hy', hy])
    |>.addEdge h₂ (by simp [hz'])
    |>.addEdge h₃ (by simp [hz', hz])

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` has vertex set `H.verts ∪ {x}`. -/
@[simp, grind =]
lemma twoHopMount_verts (H : Subgraph G) [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) (x : V)
    (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m') (h₃ : G.Adj z' z m) :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).verts = H.verts ∪ {x} := by
  simp only [twoHopMount, addEdge_verts, induce_verts, Set.union_singleton]

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` is symmetric when `H` and `G` are. As for
`mount_isSymm`, the instance unfolds the four `addEdge` layers once so that resolution can take
over. -/
instance twoHopMount_isSymm (H : Subgraph G) [H.IsSymm] [G.IsSymm] {y y' z z' : V}
    {n n' m m' : ℕ} (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts)
    (hz' : z' ∈ H.verts) (x : V) (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).IsSymm := by
  unfold twoHopMount
  infer_instance

/-- Every vertex of `H` remains a vertex of `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃`. -/
@[simp]
lemma mem_twoHopMount_verts {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts)
    {x : V} {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m}
    {x' : V} (hx' : x' ∈ H.verts) :
    x' ∈ (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).verts := by
  simp [twoHopMount_verts, hx']

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` has edge set `H.edgeSet` plus the four new
edges. -/
@[simp]
lemma twoHopMount_edgeSet (H : Subgraph G) [G.IsSymm] {y y' z z' : V}
    {n n' m m' : ℕ} (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts)
    (hz' : z' ∈ H.verts) (x : V) (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m) :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).edgeSet =
    H.edgeSet ∪ {⟨s(z', z), m⟩, ⟨s(x, z'), m'⟩, ⟨s(y', y), n⟩, ⟨s(x, y'), n'⟩} := by
  simp [twoHopMount, addEdge_edgeSet, addVerts_edgeSet]

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `x` to `y'` at time
`n'`. This and the next three lemmas lift `addEdge_edge` along the later `addEdge_le` layers, so
they need no symmetry. -/
lemma twoHopMount_adj_x_y' {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj x y' n' := by
  rw [twoHopMount]
  exact addEdge_le.right <| addEdge_le.right <| addEdge_le.right addEdge_edge

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `x` to `z'` at time
`m'`. -/
lemma twoHopMount_adj_x_z' {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj x z' m' := by
  rw [twoHopMount]
  exact addEdge_le.right addEdge_edge

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `y'` to `y` at time `n`. -/
lemma twoHopMount_adj_y'_y {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj y' y n := by
  rw [twoHopMount]
  exact addEdge_le.right <| addEdge_le.right addEdge_edge

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `z'` to `z` at time `m`. -/
lemma twoHopMount_adj_z'_z {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj z' z m := by
  rw [twoHopMount]
  exact addEdge_edge

/-- `H` is a subgraph of `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃`. -/
@[simp]
lemma twoHopMount_le {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    H ≤ H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃ :=
  addVerts_le (H := H) (s := {x})
    |>.trans (addEdge_le (h := h₀) (h₁ := by simp [hy']))
    |>.trans (addEdge_le (h := h₁) (h₁ := by simp [hy', hy]))
    |>.trans (addEdge_le (h := h₂) (h₁ := by simp [hz']))
    |>.trans (addEdge_le (h := h₃) (h₁ := by simp [hz', hz]))

/-- If dismounting `x` (via `y'`, `y` on the earliest side and `z'`, `z` on the latest side) is
temporally connected, so is `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃`. -/
theorem twoHopMount_temporallyConnected (H : Subgraph G) [H.IsSymm] [G.IsSymm] {y y' z z' : V}
    {n n' m m' : ℕ} (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts)
    (hz' : z' ∈ H.verts) (x : V) (h₀ : G.Adj x y' n') (h₁ : G.Adj y' y n) (h₂ : G.Adj x z' m')
    (h₃ : G.Adj z' z m)
    (h₄ : (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).EarliestEdge y y' n ∧ n' ≤ n)
    (h₅ : (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).LatestEdge z z' m ∧ m ≤ m') :
    H.TemporallyConnectedSubgraph →
      (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).TemporallyConnectedSubgraph := by
  intro hTC
  have hReach : ∀ a b : V, H.Reachable a b →
      (twoHopMount H hy hy' hz hz' x h₀ h₁ h₂ h₃).Reachable a b :=
    fun _ _ ↦ reachable_mono (twoHopMount_le hy hy' hz hz')
  intro a ha b hb
  simp only [twoHopMount_verts, Set.union_singleton, Set.mem_insert_iff] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact Reachable.refl _
    · exact reachable_of_extended_earliestEdge h₄.left (twoHopMount_adj_x_y' hy hy' hz hz')
        h₄.right b (hReach y b (hTC y hy b hb))
  · rcases hb with rfl | hb
    · exact reachable_of_extended_latestEdge h₅.left (twoHopMount_adj_x_z' hy hy' hz hz').symm
        h₅.right a (hReach a z (hTC a ha z hz))
    · exact hReach a b (hTC a ha b hb)

instance finite_edgeSet_twoHopMount {H : Subgraph G} [h₀ : Finite H.edgeSet] [G.IsSymm]
    {y y' z z' : V}
    {n n' m m' : ℕ} {hy : y ∈ H.verts} {hy' : y' ∈ H.verts} {hz : z ∈ H.verts}
    {hz' : z' ∈ H.verts} {x : V} {h₁ : G.Adj x y' n'} {h₂ : G.Adj y' y n} {h₃ : G.Adj x z' m'}
    {h₄ : G.Adj z' z m} :
    Finite (H.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄).edgeSet := by
  rw [H.twoHopMount_edgeSet hy hy' hz hz' x h₁ h₂ h₃ h₄]
  infer_instance

/-- Instance-free form of `twoHopMount_size`: mounting `x` back onto `H` via two hops on each
side adds at most 4 edges to `H.edgeSet`'s `Set.ncard`. -/
theorem ncard_edgeSet_twoHopMount_le {H : Subgraph G} [G.IsSymm]
    {y y' z z' : V} {n n' m m' : ℕ} {hy : y ∈ H.verts} {hy' : y' ∈ H.verts} {hz : z ∈ H.verts}
    {hz' : z' ∈ H.verts} {x : V} {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).edgeSet.ncard ≤ H.edgeSet.ncard + 4 := by
  rw [H.twoHopMount_edgeSet hy hy' hz hz' x h₀ h₁ h₂ h₃]
  have hunion := Set.ncard_union_le H.edgeSet
    ({⟨s(z', z), m⟩, ⟨s(x, z'), m'⟩, ⟨s(y', y), n⟩, ⟨s(x, y'), n'⟩} : Set (Sym2 V × ℕ))
  have hfour := Set.ncard_le_four (⟨s(z', z), m⟩ : Sym2 V × ℕ) ⟨s(x, z'), m'⟩ ⟨s(y', y), n⟩
    ⟨s(x, y'), n'⟩
  -- `|E ∪ F| ≤ |E| + |F| ≤ |E| + 4` for the four new edges `F`
  omega

/-- Mounting `x` back onto `H` via two hops on each side adds at most 4 edges. -/
theorem twoHopMount_size {H : Subgraph G} [G.IsSymm]
    {y y' z z' : V} {n n' m m' : ℕ} {hy : y ∈ H.verts} {hy' : y' ∈ H.verts} {hz : z ∈ H.verts}
    {hz' : z' ∈ H.verts} {x : V} {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m}
    [Fintype H.edgeSet] [Fintype (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).edgeSet] :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).size ≤ H.size + 4 := by
  rw [size_eq_ncard, size_eq_ncard]
  exact ncard_edgeSet_twoHopMount_le

/-- SAND 2025, §2.1 (2-hop case): re-mounting `x` via two hops on each side extends a spanner of
`H.dismount x` to a spanner of `H`, when `H` is a clique. -/
theorem twoHopDismountability {H H' : Subgraph G} [H.IsSymm] [H'.IsSymm] [G.IsSymm]
    {x y y' z z' : V} {n n' m m' : ℕ} (hx : x ∈ H.verts) (hy : y ∈ H'.verts)
    (hy' : y' ∈ H'.verts) (hz : z ∈ H'.verts) (hz' : z' ∈ H'.verts) (h₀ : H.IsCliqueSubgraph)
    (h₁ : G.Adj x y' n') (h₂ : G.Adj y' y n) (h₃ : G.Adj x z' m') (h₄ : G.Adj z' z m)
    (h₅ : H.EarliestEdge y y' n ∧ n' ≤ n ∧ H.Adj x y' n')
    (h₆ : H.LatestEdge z z' m ∧ m ≤ m' ∧ H.Adj x z' m') (h₇ : H'.IsSpannerOf (H.dismount x)) :
    (H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄).IsSpannerOf H := by
  have heq : (H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄).verts = H.verts := by
    simp [twoHopMount_verts, h₇.right.1, hx]
  have hle : (H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄) ≤ H := by
    apply le_iff_edgeSet_and_verts.mpr
    constructor
    · rw [H'.twoHopMount_edgeSet hy hy' hz hz' x h₁ h₂ h₃ h₄]
      refine Set.union_subset (edgeSet_mono (h₇.left.trans dismount_le)) ?_
      -- the four edges added by the mount are edges of `H`
      have : (s(z, z'), m) ∈ H.edgeSet := H.mem_edgeSet.mpr h₆.1.1
      have : (s(x, z'), m') ∈ H.edgeSet := H.mem_edgeSet.mpr h₆.2.2
      have : (s(y, y'), n) ∈ H.edgeSet := H.mem_edgeSet.mpr h₅.1.1
      have : (s(x, y'), n') ∈ H.edgeSet := H.mem_edgeSet.mpr h₅.2.2
      grind only [= Set.subset_def, = Sym2.eq, = Sym2.rel_iff', = Set.mem_insert_iff,
        = Prod.swap_prod_mk, = Set.mem_singleton_iff]
    · exact heq.le
  -- the mount is temporally connected, hence a spanner of the clique `H`
  have htc : (H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄).TemporallyConnectedSubgraph := by
    apply twoHopMount_temporallyConnected H' hy hy' hz hz' x
    · exact ⟨earliestEdge_of_le hle h₅.1 (twoHopMount_adj_y'_y hy hy' hz hz').symm, h₅.2.1⟩
    · exact ⟨latestEdge_of_le hle h₆.1 (twoHopMount_adj_z'_z hy hy' hz hz').symm, h₆.2.1⟩
    · exact temporallyConnectedSubgraph_of_isSpannerOf_dismount h₀ h₇
  refine ⟨hle, heq, fun u hu v hv _ ↦ htc u ?_ v ?_⟩
  · rwa [heq]
  · rwa [heq]

end TwoHopMount

section SpannerExtension

/-- Earliest side of two-hop dismountability: one or two edges of `H` such that, in any `K`
between them and `H`, whatever is reachable from `y` is reachable from `x`. -/
lemma exists_edgeSet_of_earliest {H : Subgraph G} [G.IsLoopless] [H.IsSymm] {x : V}
    (h₀ : (∃ y : V, H.EarliestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.EarliestEdge y z n ∧ H.Adj z x m ∧ m ≤ n)) :
    ∃ y ∈ H.verts, y ≠ x ∧ ∃ E : Set (Sym2 V × ℕ), E ⊆ H.edgeSet ∧ E.ncard ≤ 2 ∧
      x ∈ (Subgraph.fromEdgeSet G E).verts ∧
      ∀ (K : Subgraph G) [K.IsSymm], Subgraph.fromEdgeSet G E ≤ K → K ≤ H →
        ∀ b, K.Reachable y b → K.Reachable x b := by
  rcases h₀ with ⟨y, n, hE⟩ | ⟨y, z, n, m, hyx, hE, hzx, hmn⟩
  · -- one hop: the earliest edge `y x`
    have hadj : H.Adj y x n := hE.left
    -- `x` is a vertex of the one-edge graph, being an endpoint of the edge `s(y, x)`
    have hxmem : x ∈ (Subgraph.fromEdgeSet G {(s(y, x), n)}).verts :=
      ⟨⟨(s(y, x), n), rfl⟩, Sym2.mem_mk_right _ _⟩
    refine ⟨y, H.edge_vert hadj, hadj.ne, {(s(y, x), n)}, ?_, ?_, hxmem, ?_⟩
    · exact Set.singleton_subset_iff.mpr (H.mem_edgeSet.mpr hadj)
    · rw [Set.ncard_singleton]
      omega
    · intro K _ hK hKH b
      exact reachable_of_earliestEdge
        (earliestEdge_of_le hKH hE (adj_of_fromEdgeSet_le hK rfl (H.adj_sub hadj))) b
  · -- two hops: the earliest edge `y z`, then the edge `z x`
    have hyz : H.Adj y z n := hE.left
    -- `x` is a vertex of the two-edge graph, being an endpoint of the edge `s(z, x)`
    have hxmem : x ∈ (Subgraph.fromEdgeSet G {(s(y, z), n), (s(z, x), m)}).verts :=
      ⟨⟨(s(z, x), m), by simp⟩, Sym2.mem_mk_right _ _⟩
    refine ⟨y, H.edge_vert hyz, hyx, {(s(y, z), n), (s(z, x), m)}, ?_, Set.ncard_pair_le _ _,
      hxmem, ?_⟩
    · exact Set.insert_subset (H.mem_edgeSet.mpr hyz)
        (Set.singleton_subset_iff.mpr (H.mem_edgeSet.mpr hzx))
    · intro K _ hK hKH b
      have hKyz : K.Adj y z n := adj_of_fromEdgeSet_le hK (by simp) (H.adj_sub hyz)
      have hzx' : K.Adj z x m := adj_of_fromEdgeSet_le hK (by simp) (H.adj_sub hzx)
      exact reachable_of_extended_earliestEdge (earliestEdge_of_le hKH hE hKyz) hzx'.symm hmn b

/-- Latest side of two-hop dismountability: one or two edges of `H` such that, in any `K`
between them and `H`, whatever reaches `y` reaches `x`. -/
lemma exists_edgeSet_of_latest {H : Subgraph G} [G.IsLoopless] [H.IsSymm] {x : V}
    (h₀ : (∃ y : V, H.LatestNeighbor y x)
      ∨ (∃ (y z : V) (n m : ℕ), y ≠ x ∧ H.LatestEdge y z n ∧ H.Adj z x m ∧ n ≤ m)) :
    ∃ y ∈ H.verts, y ≠ x ∧ ∃ E : Set (Sym2 V × ℕ), E ⊆ H.edgeSet ∧ E.ncard ≤ 2 ∧
      x ∈ (Subgraph.fromEdgeSet G E).verts ∧
      ∀ (K : Subgraph G) [K.IsSymm], Subgraph.fromEdgeSet G E ≤ K → K ≤ H →
        ∀ b, K.Reachable b y → K.Reachable b x := by
  rcases h₀ with ⟨y, n, hE⟩ | ⟨y, z, n, m, hyx, hE, hzx, hmn⟩
  · -- one hop: the latest edge `y x`
    have hadj : H.Adj y x n := hE.left
    -- `x` is a vertex of the one-edge graph, being an endpoint of the edge `s(y, x)`
    have hxmem : x ∈ (Subgraph.fromEdgeSet G {(s(y, x), n)}).verts :=
      ⟨⟨(s(y, x), n), rfl⟩, Sym2.mem_mk_right _ _⟩
    refine ⟨y, H.edge_vert hadj, hadj.ne, {(s(y, x), n)}, ?_, ?_, hxmem, ?_⟩
    · exact Set.singleton_subset_iff.mpr (H.mem_edgeSet.mpr hadj)
    · rw [Set.ncard_singleton]
      omega
    · intro K _ hK hKH b
      exact reachable_of_latestEdge
        (latestEdge_of_le hKH hE (adj_of_fromEdgeSet_le hK rfl (H.adj_sub hadj))) b
  · -- two hops: the latest edge `y z`, then the edge `z x`
    have hyz : H.Adj y z n := hE.left
    -- `x` is a vertex of the two-edge graph, being an endpoint of the edge `s(z, x)`
    have hxmem : x ∈ (Subgraph.fromEdgeSet G {(s(y, z), n), (s(z, x), m)}).verts :=
      ⟨⟨(s(z, x), m), by simp⟩, Sym2.mem_mk_right _ _⟩
    refine ⟨y, H.edge_vert hyz, hyx, {(s(y, z), n), (s(z, x), m)}, ?_, Set.ncard_pair_le _ _,
      hxmem, ?_⟩
    · exact Set.insert_subset (H.mem_edgeSet.mpr hyz)
        (Set.singleton_subset_iff.mpr (H.mem_edgeSet.mpr hzx))
    · intro K _ hK hKH b
      have hKyz : K.Adj y z n := adj_of_fromEdgeSet_le hK (by simp) (H.adj_sub hyz)
      have hzx' : K.Adj z x m := adj_of_fromEdgeSet_le hK (by simp) (H.adj_sub hzx)
      exact reachable_of_extended_latestEdge (latestEdge_of_le hKH hE hKyz) hzx' hmn b

/-- SAND 2025, Theorem 2.1 and §2.1: a `{1,2}`-hop dismountable clique has a vertex `x` such that
every spanner of `H.dismount x` extends to a spanner of `H` with at most 4 more edges (1 or 2 on
each side of `x`).

The extension is `H' ⊔ fromEdgeSet G (Eₒ ∪ Eᵢ)`, where `Eₒ`, `Eᵢ` are the edge sets given by
`exists_edgeSet_of_earliest` and `exists_edgeSet_of_latest`. -/
theorem exists_isSpannerOf_of_twoHopDismountable {H : Subgraph G}
    [G.IsSymm] [G.IsLoopless] [H.IsSymm] (h₀ : H.TwoHopDismountable) :
    ∃ x ∈ H.verts, ∀ H' : Subgraph G, H'.IsSymm → H'.IsSpannerOf (H.dismount x) →
      ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerOf H ∧ K.edgeSet.ncard ≤ H'.edgeSet.ncard + 4 := by
  obtain ⟨hcl, x, he, hl⟩ := h₀
  obtain ⟨y, hy, hyx, Eₒ, hEₒ, hcₒ, hxₒ, hrₒ⟩ := exists_edgeSet_of_earliest he
  obtain ⟨z, hz, hzx, Eᵢ, hEᵢ, hcᵢ, hxᵢ, hrᵢ⟩ := exists_edgeSet_of_latest hl
  have hx : x ∈ H.verts := (fromEdgeSet_le hEₒ).left hxₒ
  refine ⟨x, hx, fun H' hH' hS ↦ ?_⟩
  -- register the hypothesis `hH'` as an instance
  have : H'.IsSymm := hH'
  have hE : Eₒ ∪ Eᵢ ⊆ H.edgeSet := Set.union_subset hEₒ hEᵢ
  have hEG : Eₒ ∪ Eᵢ ⊆ G.edgeSet := hE.trans H.edgeSet_subset
  have hF : Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ) ≤ H := fromEdgeSet_le hE
  have hFₒ : Subgraph.fromEdgeSet G Eₒ ≤ H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ) :=
    (fromEdgeSet_mono Set.subset_union_left).trans le_sup_right
  have hFᵢ : Subgraph.fromEdgeSet G Eᵢ ≤ H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ) :=
    (fromEdgeSet_mono Set.subset_union_right).trans le_sup_right
  have hKH : H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ) ≤ H :=
    sup_le (hS.left.trans dismount_le) hF
  -- the vertex set is that of `H`: `H'` has all but `x`, and `x` is an endpoint of an edge
  have hverts' : H'.verts = H.verts \ {x} := by rw [hS.right.left, dismount_verts]
  have hverts : (H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ)).verts = H.verts := by
    rw [sup_verts, hverts']
    refine Set.Subset.antisymm (Set.union_subset Set.sdiff_subset hF.left) fun v hv ↦ ?_
    by_cases hvx : v = x
    · exact Or.inr ((fromEdgeSet_mono Set.subset_union_left).left (hvx ▸ hxₒ))
    · exact Or.inl ⟨hv, hvx⟩
  -- `H'` is temporally connected on `H.verts \ {x}`
  have hH'TC : ∀ a ∈ H.verts \ {x}, ∀ b ∈ H.verts \ {x}, H'.Reachable a b := by
    intro a ha b hb
    exact temporallyConnectedSubgraph_of_isSpannerOf_dismount hcl hS a (by rwa [hverts']) b
      (by rwa [hverts'])
  refine ⟨H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ), inferInstance, ⟨hKH, hverts, ?_⟩, ?_⟩
  · intro a ha b hb _
    have hmono : ∀ u v, H'.Reachable u v →
        (H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ)).Reachable u v :=
      fun _ _ ↦ reachable_mono le_sup_left
    by_cases hax : a = x
    · subst hax
      by_cases hbx : b = a
      · exact hbx ▸ Reachable.refl _
      · -- `a` reaches `b` as `y` does, and `y ≠ a` is in `H'`
        exact hrₒ _ hFₒ hKH b (hmono y b (hH'TC y ⟨hy, hyx⟩ b ⟨hb, hbx⟩))
    · by_cases hbx : b = x
      · subst hbx
        -- `a` reaches `b` as it reaches `z`
        exact hrᵢ _ hFᵢ hKH a (hmono a z (hH'TC a ⟨ha, hax⟩ z ⟨hz, hzx⟩))
      · exact hmono a b (hH'TC a ⟨ha, hax⟩ b ⟨hb, hbx⟩)
  · -- at most `|H'| + |Eₒ| + |Eᵢ| ≤ |H'| + 2 + 2` edges
    rw [sup_edgeSet, fromEdgeSet_eq hEG]
    have hunion := Set.ncard_union_le H'.edgeSet (Eₒ ∪ Eᵢ)
    have hunion' := Set.ncard_union_le Eₒ Eᵢ
    omega

end SpannerExtension

section CliqueInduction

/-- SAND 2025, Theorem 2.1 and §2.1: generic induction on a clique. If every finite simple
proper clique subgraph that is not `{1,2}`-hop dismountable has a symmetric spanner with at most
`f n` edges (`n` its number of vertices), and `f n + 4 ≤ f (n + 1)`, then every finite simple
proper clique subgraph has a symmetric spanner with at most `f n` edges: a `{1,2}`-hop
dismountable clique is reduced to one vertex fewer at the cost of 4 edges. -/
theorem exists_isSpannerOf_ncard_le_of_forall_not_twoHopDismountable {H : Subgraph G}
    [Finite H.verts] [G.IsSymm] [G.IsLoopless] [H.IsSymm] (f : ℕ → ℕ)
    (h₀ : ∀ n, f n + 4 ≤ f (n + 1))
    (h₁ : ∀ {H' : Subgraph G} [Finite H'.verts] [Nontrivial H'.verts] [H'.IsSymm],
      H'.IsSimple → H'.IsCliqueSubgraph → H'.IsProper → ¬H'.TwoHopDismountable →
      ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerOf H' ∧ K.edgeSet.ncard ≤ f H'.verts.ncard)
    (h₂ : H.IsSimple) (h₃ : H.IsCliqueSubgraph) (h₄ : H.IsProper) :
    ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerOf H ∧ K.edgeSet.ncard ≤ f H.verts.ncard := by
  induction hn : H.verts.ncard using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    rcases le_or_gt n 1 with hle | htwo
    · -- at most one vertex: `H` has no edge, and is its own spanner
      refine ⟨H, inferInstance, ⟨le_rfl, rfl, fun _ _ _ _ h ↦ h⟩, ?_⟩
      suffices H.edgeSet = ∅ by simp [this]
      refine Set.eq_empty_of_forall_notMem fun ⟨e, m⟩ he ↦ ?_
      induction e using Sym2.ind with
      | _ a b =>
        have hadj := H.mem_edgeSet.mp he
        have hpair : ({a, b} : Set V).ncard = 2 := Set.ncard_pair hadj.ne
        have hsub : ({a, b} : Set V).ncard ≤ H.verts.ncard :=
          Set.ncard_le_ncard (Set.pair_subset (H.edge_vert hadj) (H.edge_vert' hadj))
        -- two endpoints in `H.verts`, but `H.verts.ncard = n ≤ 1`
        omega
    have : Nontrivial H.verts :=
      Set.nontrivial_coe_sort.mpr ((Set.one_lt_ncard_iff_nontrivial).mp (by omega))
    by_cases hd : H.TwoHopDismountable
    · -- dismount `x`, recurse, mount `x` back (at most 4 more edges)
      obtain ⟨x, hx, hext⟩ := exists_isSpannerOf_of_twoHopDismountable hd
      have hD : (H.dismount x).verts.ncard = n - 1 := by
        rw [dismount_verts, Set.ncard_sdiff_singleton_of_mem hx, hn]
      have hDle : (H.dismount x).toTemporalGraph ≤ H.toTemporalGraph :=
        toTemporalGraph_le dismount_le
      obtain ⟨H', hH'symm, hH'span, hH'card⟩ := ih (n - 1) (by omega) (h₂.mono hDle)
        (dismount_clique H x h₃) (h₄.mono hDle) hD
      obtain ⟨K, hKsymm, hKspan, hKcard⟩ := hext H' hH'symm hH'span
      refine ⟨K, hKsymm, hKspan, ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hH'card
      have hstep := h₀ m
      -- `|K| ≤ |H'| + 4 ≤ f m + 4 ≤ f (m + 1)`
      omega
    · -- not dismountable: the hypothesis gives the spanner directly
      have hbase := h₁ h₂ h₃ h₄ hd
      rwa [hn] at hbase

end CliqueInduction

end Subgraph

end TemporalGraph
