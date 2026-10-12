/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Dismountability.OneSidedBound

/-!
# Proved solution

Comparator matches the identically named declarations of `Challenge.lean`. This file repeats
verbatim its three definitions (`IsLocallyInjective`, `Journey`, `IsTemporalSpanner`) and proves
its two theorems from the `TemporalGraph` library.

The statement of record describes a temporal clique by a labelling `lab : Sym2 V → ℕ` of the
edges of the complete graph on a finite type `V`, locally injective, with *strict* journeys and
spanners given as finite sets of edges. The bridge to the library:

* the labelling defines a temporal graph `labGraph lab`, whose `⊤` subgraph is a finite, simple,
  proper, symmetric clique, so `Subgraph.exists_isSpannerOf_ncard_le` and
  `Subgraph.exists_isBigO_isSpannerOf` (SAND 2025, §4.1) give a symmetric spanner `K` of `⊤`;
* `K.edgeSet`, projected to `Sym2 V`, is a finite set of edges with as many elements, each edge
  having a single label (`card_edgeFinset`);
* every pair of vertices is reachable in `K`, hence strictly reachable (`K` is proper and
  symmetric, `reachable_iff_strictReachable`), and a strict walk of `K` is a journey
  (`journey_of_isStrict`).
-/

@[expose] public section

namespace TemporalCliqueSpanners

variable {V : Type}

/-- The labelling `lab` of the edges of the complete graph on `V` is *locally injective*: two
distinct edges `s(u, v)` and `s(u, w)` sharing the endpoint `u` have distinct labels. -/
def IsLocallyInjective (lab : Sym2 V → ℕ) : Prop :=
  ∀ u v w : V, u ≠ v → u ≠ w → v ≠ w → lab s(u, v) ≠ lab s(u, w)

/-- `Journey S lab t u v`: there is a journey from `u` to `v` using only edges of `S`, whose
labels are strictly increasing and all at least `t`. The empty journey goes from `u` to `u`;
otherwise the journey crosses an edge `s(u, w) ∈ S` at a time `lab s(u, w) ≥ t`, then continues
from `w` strictly after that time. -/
inductive Journey (S : Finset (Sym2 V)) (lab : Sym2 V → ℕ) : ℕ → V → V → Prop
  | nil (t : ℕ) (u : V) : Journey S lab t u u
  | cons {t : ℕ} {u w v : V} (h₀ : s(u, w) ∈ S) (h₁ : t ≤ lab s(u, w))
      (h₂ : Journey S lab (lab s(u, w) + 1) w v) : Journey S lab t u v

/-- `S` is a *temporal spanner* of the temporal clique labelled by `lab`: `S` consists of edges of
the complete graph (no diagonal pair `s(v, v)`), and every vertex `u` reaches every vertex `v`
by a journey within `S`. -/
def IsTemporalSpanner (S : Finset (Sym2 V)) (lab : Sym2 V → ℕ) : Prop :=
  (∀ e ∈ S, ¬e.IsDiag) ∧ ∀ u v : V, Journey S lab 0 u v

open TemporalGraph

/-- The temporal clique defined by a labelling: distinct `x` and `y` are joined at the single time
`lab s(x, y)`. -/
def labGraph (lab : Sym2 V → ℕ) : TemporalGraph V where
  Adj x y n := x ≠ y ∧ lab s(x, y) = n

instance labGraph_isSymm (lab : Sym2 V → ℕ) : (labGraph lab).IsSymm :=
  .of_adj fun _ _ _ h ↦ ⟨h.1.symm, Sym2.eq_swap ▸ h.2⟩

instance labGraph_isLoopless (lab : Sym2 V → ℕ) : (labGraph lab).IsLoopless :=
  ⟨fun _ ↦ ⟨fun _ h ↦ h.1 rfl⟩⟩

variable {lab : Sym2 V → ℕ}

/-- The clique `⊤` of `labGraph lab` is simple: each edge has the single time `lab`. -/
theorem top_isSimple : (⊤ : (labGraph lab).Subgraph).IsSimple :=
  fun _ _ _ _ h₁ h₂ ↦ h₁.2.symm.trans h₂.2

/-- The clique `⊤` of `labGraph lab` is proper when `lab` is locally injective. -/
theorem top_isProper (h₀ : IsLocallyInjective lab) : (⊤ : (labGraph lab).Subgraph).IsProper := by
  intro x y z n h₁ h₂
  by_contra hyz
  exact h₀ x y z h₁.1 h₂.1 hyz (h₁.2.trans h₂.2.symm)

/-- `labGraph lab` is a clique: distinct vertices are joined, at time `lab`. -/
theorem top_isCliqueSubgraph : (⊤ : (labGraph lab).Subgraph).IsCliqueSubgraph :=
  fun x _ y _ hxy ↦ ⟨lab s(x, y), hxy, rfl⟩

/-- An edge of a subgraph of `labGraph lab` is off the diagonal and carries its label. -/
theorem of_mem_edgeSet {K : (labGraph lab).Subgraph} {p : Sym2 V} {n : ℕ}
    (h₀ : (p, n) ∈ K.edgeSet) : ¬p.IsDiag ∧ lab p = n := by
  obtain ⟨x, y, rfl, hadj⟩ := h₀
  obtain ⟨hxy, hlab⟩ := K.adj_sub hadj
  exact ⟨Sym2.mk_isDiag_iff.not.mpr hxy, hlab⟩

/-- The edges of a subgraph `K` of `labGraph lab`, forgetting their (determined) times. -/
noncomputable def edgeFinset [Finite V] (K : (labGraph lab).Subgraph) : Finset (Sym2 V) :=
  (Set.toFinite (Prod.fst '' K.edgeSet)).toFinset

theorem mem_edgeFinset [Finite V] {K : (labGraph lab).Subgraph} {p : Sym2 V} :
    p ∈ edgeFinset K ↔ p ∈ Prod.fst '' K.edgeSet :=
  Set.Finite.mem_toFinset _

/-- Forgetting the times loses no edge: each edge of `labGraph lab` has a single time. -/
theorem card_edgeFinset [Finite V] (K : (labGraph lab).Subgraph) :
    (edgeFinset K).card = K.edgeSet.ncard := by
  rw [edgeFinset, ← Set.ncard_eq_toFinset_card]
  refine Set.InjOn.ncard_image fun ⟨p, n⟩ hp ⟨p', n'⟩ hp' h ↦ ?_
  simp only at h
  subst h
  rw [← (of_mem_edgeSet hp).2, ← (of_mem_edgeSet hp').2]

/-- A strict walk of `K` from `x`, starting no earlier than `t` and ending at `y` at time `m`,
followed by a journey from `y` after `m`, is a journey from `x` after `t`. -/
theorem journey_of_isStrict [Finite V] {K : (labGraph lab).Subgraph} {x y : V} {n m : ℕ}
    (p : K.NonemptyTemporalWalk x n y m) (hp : p.IsStrict) :
    ∀ w, Journey (edgeFinset K) lab (m + 1) y w → ∀ t ≤ n, Journey (edgeFinset K) lab t x w := by
  induction p with
  | single h =>
    intro w hw t ht
    have hlab := (K.adj_sub h).2
    refine .cons (mem_edgeFinset.mpr ⟨_, Subgraph.Adj.mem_edgeSet h, rfl⟩) (hlab ▸ ht) (hlab ▸ hw)
  | @step y z n m k p h h₁ ih =>
    intro w hw t ht
    have hlab := (K.adj_sub h).2
    obtain ⟨hlt, hp'⟩ : m < k ∧ p.IsStrict := hp
    refine ih hp' w ?_ t ht
    exact .cons (mem_edgeFinset.mpr ⟨_, Subgraph.Adj.mem_edgeSet h, rfl⟩) (hlab ▸ hlt) (hlab ▸ hw)

/-- A symmetric spanner `K` of the clique `⊤` of `labGraph lab` gives a temporal spanner, its edge
set. -/
theorem isTemporalSpanner_edgeFinset [Finite V] (h₀ : IsLocallyInjective lab)
    {K : (labGraph lab).Subgraph} [K.IsSymm] (h₁ : K.IsSpannerOf ⊤) :
    IsTemporalSpanner (edgeFinset K) lab := by
  refine ⟨fun e he ↦ ?_, fun u v ↦ ?_⟩
  · obtain ⟨⟨p, n⟩, hp, rfl⟩ := mem_edgeFinset.mp he
    exact (of_mem_edgeSet hp).1
  -- `u` reaches `v` in the clique, hence in `K`, hence strictly in `K` (`K` is proper)
  have hTC := temporallyConnected_of_isClique _ (top_isCliqueSubgraph (lab := lab))
  have hreach : K.Reachable u v := h₁.2.2 u trivial v trivial (hTC u trivial v trivial)
  have hprop : K.IsProper := (top_isProper h₀).mono (Subgraph.toTemporalGraph_le h₁.1)
  obtain ⟨n, m, q, hq⟩ := (reachable_iff_strictReachable hprop).mp hreach
  cases q with
  | nil => exact .nil 0 u
  | ofNonempty p => exact journey_of_isStrict p hq v (.nil _ v) 0 (Nat.zero_le _)

/-- Explicit bound: every temporal clique on `n` vertices admits a temporal spanner with at most
`2 n ⌈log₂ n⌉ + 4 n` edges. -/
theorem exists_isTemporalSpanner_card_le (V : Type) [Finite V] (lab : Sym2 V → ℕ)
    (h : IsLocallyInjective lab) :
    ∃ S : Finset (Sym2 V), IsTemporalSpanner S lab ∧
      S.card ≤ 2 * Nat.card V * Nat.clog 2 (Nat.card V) + 4 * Nat.card V := by
  obtain ⟨K, hKsymm, hK, hcard⟩ := Subgraph.exists_isSpannerOf_ncard_le (H := ⊤)
    (top_isSimple (lab := lab)) top_isCliqueSubgraph (top_isProper h)
  refine ⟨edgeFinset K, isTemporalSpanner_edgeFinset h hK, ?_⟩
  rw [card_edgeFinset]
  simpa [Subgraph.top_verts, Set.ncard_univ] using hcard

open Asymptotics Filter in
/-- Casteigts–Peters–Schoeters (ICALP 2019), reproved by Carnevale–Casteigts–Corsini (SAND 2025,
§4.1): temporal cliques on `n` vertices admit temporal spanners of size `O(n log n)`. The bound
`f` is chosen once, uniformly over all temporal cliques. -/
theorem exists_isBigO_isTemporalSpanner :
    ∃ f : ℕ → ℕ, (fun n ↦ (f n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ) * Real.log n) ∧
      ∀ (V : Type) [Finite V] (lab : Sym2 V → ℕ), IsLocallyInjective lab →
        ∃ S : Finset (Sym2 V), IsTemporalSpanner S lab ∧ S.card ≤ f (Nat.card V) := by
  obtain ⟨f, hf, hall⟩ := Subgraph.exists_isBigO_isSpannerOf.{0}
  refine ⟨f, hf, fun V _ lab h ↦ ?_⟩
  obtain ⟨K, hKsymm, hK, hcard⟩ := hall (H := (⊤ : (labGraph lab).Subgraph))
    (top_isSimple (lab := lab)) top_isCliqueSubgraph (top_isProper h)
  refine ⟨edgeFinset K, isTemporalSpanner_edgeFinset h hK, ?_⟩
  rw [card_edgeFinset]
  simpa [Subgraph.top_verts, Set.ncard_univ] using hcard

end TemporalCliqueSpanners
