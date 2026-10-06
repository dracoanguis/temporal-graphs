/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Basic
import TemporalGraph.Subgraph
import TemporalGraph.Connectivity.Subgraph
import TemporalGraph.Dismountability.Basic

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
* `TemporalGraph.Subgraph.exists_isSpannerOf_of_twoHopDismountable` : SAND 2025, Theorem 2.1
  and §2.1, a `{1,2}`-hop dismountable clique has a vertex `x` such that every spanner of
  `H.dismount x` extends to a spanner of `H` with at most 4 more edges. The witness on each side
  (earliest, latest) is a set of 1 or 2 edges, so the mixed 1/2-hop cases are handled at once.

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
@[simp, grind =]
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

/-- `H.mount hy hz x h₀ h₁` is symmetric when `H` and `G` are. -/
-- `mount` is a plain `def`, so instance resolution cannot see the `addEdge`/`addVerts`
-- layers it is built from; this instance unfolds it once and hands the goal back to resolution.
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
lemma mount_edge (H : Subgraph G) [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H hy hz x h₀ h₁).Adj x y n := by
  simp only [mount, addEdge, induce_verts, Set.union_singleton, induce_Adj,
    Set.mem_insert_iff, true_or, true_and, and_true, and_self, or_true]

/-- `H.mount hy hz x h₀ h₁` contains the edge from `z` to `x` at time `m`. -/
lemma mount_edge' (H : Subgraph G) [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (mount H hy hz x h₀ h₁).Adj z x m := by
  rw [mount]
  apply addEdge_edge

/-- `H` is a subgraph of `H.mount hy hz x h₀ h₁`. -/
lemma mount_le {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) {h₀ : G.Adj y x n} {h₁ : G.Adj z x m} :
    H ≤ H.mount hy hz x h₀ h₁ := by
  unfold mount
  have h := addVerts_le' H {x}
  have h' := h.trans <| addEdge_le' (H.addVerts {x}) h₀ (by simp [hy])
  exact le_trans h' addEdge_le

/-- `H.mount hy hz x h₀ h₁` has edge set `H.edgeSet` plus the two new edges `z x` at `m` and `y x`
at `n`. -/
@[simp]
lemma mount_edgeSet (H : Subgraph G) [G.IsSymm] {x y z : V} {n m : ℕ}
    (hy : y ∈ H.verts) (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m) :
    (H.mount hy hz x h₀ h₁).edgeSet = H.edgeSet ∪ {⟨s(z,x), m⟩, ⟨s(y,x), n⟩} := by
  simp [mount, addEdge_edgeSet, addVerts_edgeSet]

/-- If dismounting `x` from `H` (via its earliest edge to `y` and latest edge to `z`) is
temporally connected, so is `H.mount hy hz x h₀ h₁`, provided those edges are indeed the earliest
and latest edges at `x`. -/
theorem mount_tc (H : Subgraph G) [H.IsSymm] [G.IsSymm] {x y z : V} {n m : ℕ} (hy : y ∈ H.verts)
    (hz : z ∈ H.verts) (h₀ : G.Adj y x n) (h₁ : G.Adj z x m)
    (h₂ : (mount H hy hz x h₀ h₁).EarliestEdge y x n)
    (h₃ : (mount H hy hz x h₀ h₁).LatestEdge z x m) :
    H.TemporallyConnectedSubgraph → (mount H hy hz x h₀ h₁).TemporallyConnectedSubgraph := by
  intro hTC
  have hReach : ∀ a b : V, H.Reachable a b → (mount H hy hz x h₀ h₁).Reachable a b :=
    fun _ _ ↦ reachable_of_le_reachable (mount_le hy hz)
  intro a ha b hb
  simp only [mount_verts, Set.union_singleton, Set.mem_insert_iff] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact reachable_of_self _
    · exact reachable_of_earliestEdge h₂ b (hReach y b (hTC y hy b hb))
  · rcases hb with rfl | hb
    · exact reachable_of_latestEdge h₃ a (hReach a z (hTC a ha z hz))
    · exact hReach a b (hTC a ha b hb)

instance {H : Subgraph G} [h₀ : Finite H.edgeSet] [G.IsSymm] {x y z : V}
    {n m : ℕ} {hy : y ∈ H.verts} {hz : z ∈ H.verts} {h₁ : G.Adj y x n} {h₂ : G.Adj z x m} :
    Finite (H.mount hy hz x h₁ h₂).edgeSet := by
  conv =>
    rhs ; rw [H.mount_edgeSet]
  apply Set.Finite.union
  · trivial
  · simp only [Set.finite_insert, Set.finite_singleton]

/-- Instance-free form of `mount_size`: mounting `x` back onto `H` adds at most 2 edges to
`H.edgeSet`'s `Set.ncard`. -/
theorem ncard_edgeSet_mount_le {H : Subgraph G} [G.IsSymm] {x y z : V} {n m : ℕ}
    {hy : y ∈ H.verts} {hz : z ∈ H.verts} {h₀ : G.Adj y x n} {h₁ : G.Adj z x m} :
    (H.mount hy hz x h₀ h₁).edgeSet.ncard ≤ H.edgeSet.ncard + 2 := by
  rw [H.mount_edgeSet]
  have hun := Set.ncard_union_le H.edgeSet ({⟨s(z, x), m⟩, ⟨s(y, x), n⟩} : Set (Sym2 V × ℕ))
  have hcard := ncard_pair_le (⟨s(z, x), m⟩ : Sym2 V × ℕ) ⟨s(y, x), n⟩
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
theorem dismountability {H H' : Subgraph G} [H.IsSymm] [H'.IsSymm] [G.IsSymm] [G.IsLoopless]
    {x y z : V} (hx : x ∈ H.verts) (hy : y ∈ H'.verts) (hz : z ∈ H'.verts) {n m : ℕ}
    (h₀ : H.IsCliqueSubgraph) (h₁ : G.Adj y x n) (h₂ : G.Adj z x m) (h₃ : H.EarliestEdge y x n)
    (h₄ : H.LatestEdge z x m) (h₅ : H'.IsSpannerOf (H.dismount x)) :
    H'.mount hy hz x h₁ h₂ |>.IsSpannerOf H := by
  have heq : (H'.mount hy hz x h₁ h₂).verts = H.verts := by simp only [mount_verts, h₅.right.1,
    induce_verts, Set.union_singleton, hx, Set.insert_sdiff_self_of_mem]
  have hle : H'.mount hy hz x h₁ h₂ ≤ H := by
    apply le_iff_edgeSet_and_verts.mpr
    constructor
    · rw [H'.mount_edgeSet]
      have hsplit : H.edgeSet = H.edgeSet ∪ H.edgeSet := by simp
      rw [hsplit]
      apply Set.union_subset_union
      · apply edgeSet_le
        apply le_trans h₅.left dismount_le
      · -- the two edges added by the mount are edges of `H`
        have : (s(z, x), m) ∈ H.edgeSet := H.mem_edgeSet.mpr h₄.left
        have : (s(y, x), n) ∈ H.edgeSet := H.mem_edgeSet.mpr h₃.left
        grind only [= Sym2.eq, = Set.subset_def, = Set.mem_insert_iff, = Set.mem_singleton_iff]
    · simp only [mount_verts, h₅.right.1, induce_verts, Set.union_singleton, hx,
      Set.insert_sdiff_self_of_mem, subset_refl]
  have htc : (H'.mount hy hz x h₁ h₂).TemporallyConnectedSubgraph := by
    apply mount_tc H'
    · apply earliestEdge_of_ge _ h₃
      · exact (mount_edge H' hy hz h₁ h₂).symm
      · trivial
    · apply latestEdge_of_ge _ h₄
      · apply mount_edge'
      · trivial
    · have hdisTC : (H.dismount x).TemporallyConnectedSubgraph :=
        TemporalGraph.temporallyConnected_of_isClique _ (dismount_clique H x h₀)
      intro u hu v hv
      obtain ⟨heqV, hspan⟩ := h₅.right
      rw [heqV] at hu hv
      exact hspan u hu v hv (hdisTC u hu v hv)
  refine ⟨hle, heq, ?_⟩
  intro u hu v hv _
  exact htc u (by rw [heq]; exact hu) v (by rw [heq]; exact hv)

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

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` is symmetric when `H` and `G` are. -/
-- Same as `mount_isSymm`: resolution stops at the `def`, so unfold the four `addEdge`
-- layers once and let the `addEdge_isSymm`/`addVerts_isSymm` instances take over.
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
    H.edgeSet ∪ {⟨s(z', z), m⟩,  ⟨s(x, z'), m'⟩, ⟨s(y',y), n⟩, ⟨s(x,y'), n'⟩} := by
  simp [twoHopMount, addEdge_edgeSet, addVerts_edgeSet]

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `x` to `y'` at time
`n'`. -/
-- The four edges below are the ones `twoHopMount` inserts directly, so each is obtained by
-- lifting `addEdge_edge` along the later `addEdge_le` layers: no symmetry needed.
lemma twoHopMount_edge {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj x y' n' := by
  rw [twoHopMount]
  exact addEdge_le.right <| addEdge_le.right <| addEdge_le.right addEdge_edge

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `x` to `z'` at time
`m'`. -/
lemma twoHopMount_edge' {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj x z' m' := by
  rw [twoHopMount]
  exact addEdge_le.right addEdge_edge

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `y'` to `y` at time `n`. -/
lemma twoHopMount_edge'' {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
    (hy : y ∈ H.verts) (hy' : y' ∈ H.verts) (hz : z ∈ H.verts) (hz' : z' ∈ H.verts) {x : V}
    {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'} {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).Adj y' y n := by
  rw [twoHopMount]
  exact addEdge_le.right <| addEdge_le.right addEdge_edge

/-- `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃` contains the edge from `z'` to `z` at time `m`. -/
lemma twoHopMount_edge''' {H : Subgraph G} [G.IsSymm] {y y' z z' : V} {n n' m m' : ℕ}
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
  addVerts_le' H {x}
    |>.trans (addEdge_le' _ h₀ (by simp [hy']))
    |>.trans (addEdge_le' _ h₁ (by simp [hy', hy]))
    |>.trans (addEdge_le' _ h₂ (by simp [hz']))
    |>.trans (addEdge_le' _ h₃ (by simp [hz', hz]))

/-- If dismounting `x` (via `y'`, `y` on the earliest side and `z'`, `z` on the latest side) is
temporally connected, so is `H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃`. -/
theorem twoHopMount_TC (H : Subgraph G) [H.IsSymm] [G.IsSymm] {y y' z z' : V}
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
    fun _ _ ↦ reachable_of_le_reachable (twoHopMount_le hy hy' hz hz')
  intro a ha b hb
  simp only [twoHopMount_verts, Set.union_singleton, Set.mem_insert_iff] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact reachable_of_self _
    · exact reachable_of_extended_earliestEdge h₄.left (twoHopMount_edge hy hy' hz hz')
        h₄.right b (hReach y b (hTC y hy b hb))
  · rcases hb with rfl | hb
    · exact reachable_of_extended_latestEdge h₅.left (twoHopMount_edge' hy hy' hz hz').symm
        h₅.right a (hReach a z (hTC a ha z hz))
    · exact hReach a b (hTC a ha b hb)

instance {H : Subgraph G} [h₀ : Finite H.edgeSet] [G.IsSymm] {y y' z z' : V}
    {n n' m m' : ℕ} {hy : y ∈ H.verts} {hy' : y' ∈ H.verts} {hz : z ∈ H.verts}
    {hz' : z' ∈ H.verts} {x : V} {h₁ : G.Adj x y' n'} {h₂ : G.Adj y' y n} {h₃ : G.Adj x z' m'}
    {h₄ : G.Adj z' z m} :
    Finite (H.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄).edgeSet := by
  conv =>
    rhs ; rw [H.twoHopMount_edgeSet hy hy' hz hz' x h₁ h₂ h₃ h₄]
  apply Set.Finite.union
  · trivial
  · simp only [Set.finite_insert, Set.finite_singleton]

/-- Instance-free form of `twoHopMount_size`: mounting `x` back onto `H` via two hops on each
side adds at most 4 edges to `H.edgeSet`'s `Set.ncard`. -/
theorem ncard_edgeSet_twoHopMount_le {H : Subgraph G} [G.IsSymm]
    {y y' z z' : V} {n n' m m' : ℕ} {hy : y ∈ H.verts} {hy' : y' ∈ H.verts} {hz : z ∈ H.verts}
    {hz' : z' ∈ H.verts} {x : V} {h₀ : G.Adj x y' n'} {h₁ : G.Adj y' y n} {h₂ : G.Adj x z' m'}
    {h₃ : G.Adj z' z m} :
    (H.twoHopMount hy hy' hz hz' x h₀ h₁ h₂ h₃).edgeSet.ncard ≤ H.edgeSet.ncard + 4 := by
  rw [H.twoHopMount_edgeSet hy hy' hz hz' x h₀ h₁ h₂ h₃]
  have hun := Set.ncard_union_le H.edgeSet
    ({⟨s(z', z), m⟩, ⟨s(x, z'), m'⟩, ⟨s(y', y), n⟩, ⟨s(x, y'), n'⟩} : Set (Sym2 V × ℕ))
  have hcard := ncard_le_four (⟨s(z', z), m⟩ : Sym2 V × ℕ) ⟨s(x, z'), m'⟩ ⟨s(y', y), n⟩
    ⟨s(x, y'), n'⟩
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
theorem twoHopDismountability {H H' : Subgraph G} [H.IsSymm] [H'.IsSymm] [G.IsSymm] [G.IsLoopless]
    {x y y' z z' : V} (hx : x ∈ H.verts) (hy : y ∈ H'.verts) (hy' : y' ∈ H'.verts)
    (hz : z ∈ H'.verts) (hz' : z' ∈ H'.verts) {n n' m m' : ℕ}
    (h₀ : H.IsCliqueSubgraph) (h₁ : G.Adj x y' n') (h₂ : G.Adj y' y n) (h₃ : G.Adj x z' m')
    (h₄ : G.Adj z' z m) (h₅ : H.EarliestEdge y y' n ∧ n' ≤ n ∧ H.Adj x y' n')
    (h₆ : H.LatestEdge z z' m ∧ m ≤ m' ∧ H.Adj x z' m') (h₇ : H'.IsSpannerOf (H.dismount x)) :
    H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄ |>.IsSpannerOf H := by
  have heq : (H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄).verts = H.verts := by
    simp [twoHopMount_verts, h₇.right.1, hx]
  have hle : (H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄) ≤ H := by
    apply le_iff_edgeSet_and_verts.mpr
    constructor
    · rw [H'.twoHopMount_edgeSet hy hy' hz hz' x h₁ h₂ h₃ h₄]
      have hsplit : H.edgeSet = H.edgeSet ∪ H.edgeSet := by simp
      rw [hsplit]
      apply Set.union_subset_union
      · apply edgeSet_le
        apply le_trans h₇.left dismount_le
      · -- the four edges added by the mount are edges of `H`
        have : (s(z, z'), m) ∈ H.edgeSet := H.mem_edgeSet.mpr h₆.1.1
        have : (s(x, z'), m') ∈ H.edgeSet := H.mem_edgeSet.mpr h₆.2.2
        have : (s(y, y'), n) ∈ H.edgeSet := H.mem_edgeSet.mpr h₅.1.1
        have : (s(x, y'), n') ∈ H.edgeSet := H.mem_edgeSet.mpr h₅.2.2
        grind only [= Set.subset_def, = Sym2.eq, = Sym2.rel_iff', = Set.mem_insert_iff,
          = Prod.swap_prod_mk, = Set.mem_singleton_iff]
    · exact heq.le
  have htc : (H'.twoHopMount hy hy' hz hz' x h₁ h₂ h₃ h₄).TemporallyConnectedSubgraph := by
    apply twoHopMount_TC H' hy hy' hz hz' x
    · apply And.intro
      · apply earliestEdge_of_ge _ h₅.left
        · exact (twoHopMount_edge'' hy hy' hz hz').symm
        · trivial
      · exact h₅.2.1
    · apply And.intro
      · apply latestEdge_of_ge _ h₆.left
        · exact (twoHopMount_edge''' hy hy' hz hz').symm
        · trivial
      · exact h₆.2.1
    · have hdisTC : (H.dismount x).TemporallyConnectedSubgraph :=
        TemporalGraph.temporallyConnected_of_isClique _ (dismount_clique H x h₀)
      intro u hu v hv
      obtain ⟨heqV, hspan⟩ := h₇.right
      rw [heqV] at hu hv
      exact hspan u hu v hv (hdisTC u hu v hv)
  refine ⟨hle, heq, ?_⟩
  intro u hu v hv _
  exact htc u (by rw [heq]; exact hu) v (by rw [heq]; exact hv)

end TwoHopMount

section TwoHopDismountability

/-- SAND 2025, Theorem 2.1 and §2.1: a `{1,2}`-hop dismountable clique has a vertex `x` such that
every spanner of `H.dismount x` extends to a spanner of `H` with at most 4 more edges (1 or 2 on
each side of `x`). -/
theorem exists_isSpannerOf_of_twoHopDismountable {H : Subgraph G}
    [G.IsSymm] [G.IsLoopless] [H.IsSymm] (h₀ : H.TwoHopDismountable) :
    ∃ x ∈ H.verts, ∀ H' : Subgraph G, H'.IsSymm → H'.IsSpannerOf (H.dismount x) →
      ∃ K : Subgraph G, K.IsSymm ∧ K.IsSpannerOf H ∧ K.edgeSet.ncard ≤ H'.edgeSet.ncard + 4 := by
  obtain ⟨hcl, x, he, hl⟩ := h₀
  obtain ⟨y, hy, hyx, Eₒ, hEₒ, hcₒ, hxₒ, hrₒ⟩ := exists_edgeSet_of_earliest he
  obtain ⟨z, hz, hzx, Eᵢ, hEᵢ, hcᵢ, hxᵢ, hrᵢ⟩ := exists_edgeSet_of_latest hl
  have hx : x ∈ H.verts := (fromEdgeSet_le hEₒ).left hxₒ
  refine ⟨x, hx, fun H' hH' hS => ?_⟩
  have := hH'
  have hE : Eₒ ∪ Eᵢ ⊆ H.edgeSet := Set.union_subset hEₒ hEᵢ
  have hEG : Eₒ ∪ Eᵢ ⊆ G.edgeSet := by
    rintro ⟨p, n⟩ hp
    induction p using Sym2.ind with
    | _ a b => exact G.mem_edgeSet.mpr (H.adj_sub (H.mem_edgeSet.mp (hE hp)))
  have hF : Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ) ≤ H := fromEdgeSet_le hE
  have hFₒ : Subgraph.fromEdgeSet G Eₒ ≤ H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ) :=
    (fromEdgeSet_mono Set.subset_union_left).trans le_sup_right
  have hFᵢ : Subgraph.fromEdgeSet G Eᵢ ≤ H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ) :=
    (fromEdgeSet_mono Set.subset_union_right).trans le_sup_right
  have hKH : H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ) ≤ H :=
    sup_le (hS.left.trans dismount_le) hF
  -- the vertex set is that of `H`: `H'` has all but `x`, and `x` is an endpoint of an edge
  have hverts : (H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ)).verts = H.verts := by
    rw [sup_verts, hS.right.left, dismount_verts]
    refine Set.Subset.antisymm (Set.union_subset Set.sdiff_subset hF.left) fun v hv ↦ ?_
    by_cases hvx : v = x
    · exact Or.inr ((fromEdgeSet_mono Set.subset_union_left).left (hvx ▸ hxₒ))
    · exact Or.inl ⟨hv, hvx⟩
  -- `H'` is temporally connected on `H.verts \ {x}`
  have hdisTC : (H.dismount x).TemporallyConnectedSubgraph :=
    TemporalGraph.temporallyConnected_of_isClique _ (dismount_clique H x hcl)
  have hH'TC : ∀ a ∈ H.verts \ {x}, ∀ b ∈ H.verts \ {x}, H'.Reachable a b := by
    intro a ha b hb
    rw [← dismount_verts] at ha hb
    exact hS.right.right a ha b hb (hdisTC a ha b hb)
  refine ⟨H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ), inferInstance, ⟨hKH, hverts, ?_⟩, ?_⟩
  · intro a ha b hb _
    have hmono : ∀ u v, H'.Reachable u v →
        (H' ⊔ Subgraph.fromEdgeSet G (Eₒ ∪ Eᵢ)).Reachable u v :=
      fun _ _ ↦ reachable_of_le_reachable le_sup_left
    by_cases hax : a = x
    · subst hax
      by_cases hbx : b = a
      · exact hbx ▸ reachable_of_self _
      -- `a` reaches `b` as `y` does, and `y ≠ a` is in `H'`
      · exact hrₒ _ hFₒ hKH b (hmono y b (hH'TC y ⟨hy, hyx⟩ b ⟨hb, hbx⟩))
    · by_cases hbx : b = x
      · subst hbx
        -- `a` reaches `b` as it reaches `z`
        exact hrᵢ _ hFᵢ hKH a (hmono a z (hH'TC a ⟨ha, hax⟩ z ⟨hz, hzx⟩))
      · exact hmono a b (hH'TC a ⟨ha, hax⟩ b ⟨hb, hbx⟩)
  · rw [sup_edgeSet, fromEdgeSet_eq hEG]
    have h₁ := Set.ncard_union_le H'.edgeSet (Eₒ ∪ Eᵢ)
    have h₂ := Set.ncard_union_le Eₒ Eᵢ
    omega

end TwoHopDismountability

end Subgraph

end TemporalGraph
