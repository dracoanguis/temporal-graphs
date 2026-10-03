/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
import TemporalGraph.Dismountability.OneSided
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Size of one-sided spanners

This module bounds the size of the one-sided spanner built by `oneSidedDismountability`
(`TemporalGraph/Dismountability/OneSided.lean`) by repeated halving. The strategy is due to
Angrick et al. (ESA 2024), as recalled in SAND 2025, §4.1: splitting the source part of a
bi-clique into two halves of size `⌈n / 2⌉` and `⌊n / 2⌋`, then dismounting the other half's
targets at two edges each, yields the recurrence
`size(n) ≤ 2 * size(n / 2) + O(n)`. `spannerBound` is this recurrence made explicit (with the
`O(n)` term instantiated to `2 * n`), `spannerBound_le` solves it in closed form,
`spannerBound n ≤ 2 * n * ⌈log₂ n⌉ + n`, and `exists_isSpannerFromTo_ncard_le` proves it is
actually realized by a one-sided spanner of any balanced temporal bi-clique, yielding the
`O(n log n)` bound `exists_isBigO_isOneSidedSpannerBound`.

## Main definitions

* `TemporalGraph.Subgraph.spannerBound` : the SAND 2025, §4.1 recurrence on balanced one-sided
  instances.
* `TemporalGraph.Subgraph.IsOneSidedSpannerBound` : `f` bounds the one-sided spanners of every
  finite simple temporal bi-clique with balanced nonempty parts of size `n` by `f n`.

## Main results

* `TemporalGraph.Subgraph.exists_isSpannerFromTo_of_singleton` : the base case of the recursion,
  a single edge is a one-sided spanner of itself.
* `TemporalGraph.Subgraph.spannerBound_le` : closed form, `spannerBound n ≤ 2 n ⌈log₂ n⌉ + n`.
* `TemporalGraph.Subgraph.spannerBound_two_pow` : the bound is attained exactly at powers of two.
* `TemporalGraph.Subgraph.spannerBound_isBigO` : `spannerBound` is `O(n log n)`.
* `TemporalGraph.Subgraph.exists_isSpannerFromTo_ncard_le` : the recursion itself, bounding the
  one-sided spanner of a balanced bi-clique by `spannerBound`.
* `TemporalGraph.Subgraph.isOneSidedSpannerBound_spannerBound` : `spannerBound` is a one-sided
  spanner bound.
* `TemporalGraph.Subgraph.exists_isBigO_isOneSidedSpannerBound` : SAND 2025, §4.1 (Angrick et
  al.): temporal bi-cliques admit one-sided spanners of size `O(n log n)`.

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025
  (LIPIcs 330, doi:10.4230/LIPIcs.SAND.2025.6), §4.1.
* Angrick, Bals, Friedrich, Gawendowicz, Hastrich, Klodt, Lenzner, Schmidt, Skretas & Wells,
  *How to Reduce Temporal Cliques to Find Sparse Spanners*, ESA 2024 (LIPIcs 308,
  doi:10.4230/LIPIcs.ESA.2024.11, arXiv:2402.13624) — origin of the one-sided strategy.
-/

universe u

namespace TemporalGraph

namespace Subgraph

variable {V : Type u} {G : TemporalGraph V}

/-- SAND 2025, §4.1 (base case of the one-sided recursion): a single edge of `H` from `a` to `b`
at time `n` is itself a one-sided spanner from `{a}` to `{b}`, with at most one edge. -/
lemma exists_isSpannerFromTo_of_singleton {H : Subgraph G} [G.IsSymm] [H.IsSymm] {a b : V} {n : ℕ}
    (h : H.Adj a b n) :
    ∃ H' : Subgraph G, H'.IsSymm ∧ H'.IsSpannerFromTo H {a} {b} ∧ H'.edgeSet.ncard ≤ 1 := by
  have ha : a ∈ H.verts := H.edge_vert h
  have hb : b ∈ H.verts := H.edge_vert' h
  set H' := ((⊥ : Subgraph G).addVerts {a, b}).addEdge (H.adj_sub h) (by simp) with hH'
  refine ⟨H', inferInstance, ⟨?_, ?_⟩, ?_⟩
  · -- `H' ≤ H`: its one edge is `H`'s own, and its two vertices are `H`'s
    rw [le_iff_edgeSet_and_verts]
    refine ⟨?_, ?_⟩
    · rw [hH', addEdge_edgeSet, addVerts_edgeSet, bot_edgeSet, insert_empty_eq]
      exact Set.singleton_subset_iff.mpr (Adj.mem_edgeSet h)
    · rw [hH', addEdge_verts, addVerts_verts, bot_verts, Set.empty_union]
      rintro v (rfl | rfl) <;> assumption
  · -- `{a}` reaches `{b}`, through the edge just added
    rintro x rfl y rfl -
    refine reachable_of_nonempty_NonemptyTemporalWalk ⟨n, n, ⟨.Single ?_⟩⟩
    rw [hH']; exact addEdge_edge
  · -- at most one edge: `H'`'s edge set is `∅` plus the one edge just inserted
    rw [hH']; simp

/-- The recurrence of SAND 2025, §4.1, on balanced one-sided instances of size `n`: split the
source in halves `⌈n/2⌉` and `⌊n/2⌋`; in each half, dismount the other half of the targets, at
two edges each. -/
def spannerBound : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => spannerBound ((n + 3) / 2) + spannerBound ((n + 2) / 2) + 2 * (n + 2)
decreasing_by all_goals omega

@[simp, grind =]
lemma spannerBound_zero : spannerBound 0 = 1 := by simp [spannerBound]

@[simp, grind =]
lemma spannerBound_one : spannerBound 1 = 1 := by simp [spannerBound]

/-- The defining equation of `spannerBound` at `n + 2`. -/
@[simp, grind =]
lemma spannerBound_add_two (n : ℕ) :
    spannerBound (n + 2) =
      spannerBound ((n + 3) / 2) + spannerBound ((n + 2) / 2) + 2 * (n + 2) := by
  simp [spannerBound]

/-- `clog 2` drops by at least one when halving with a ceiling, for `n ≥ 2`: used to bound
`spannerBound`'s two recursive calls against the same logarithm as `n`. -/
private lemma clog_half_le {n : ℕ} (h : 2 ≤ n) :
    Nat.clog 2 ((n + 1) / 2) + 1 ≤ Nat.clog 2 n := by
  have hc1 : 1 ≤ Nat.clog 2 n := Nat.clog_pos one_lt_two h
  have hn2c : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog one_lt_two n
  have hpow : (2 : ℕ) ^ Nat.clog 2 n = 2 ^ (Nat.clog 2 n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hhalf : (n + 1) / 2 ≤ 2 ^ (Nat.clog 2 n - 1) := by omega
  have hle := Nat.clog_le_of_le_pow hhalf
  omega

/-- Closed form: `spannerBound n ≤ 2 n ⌈log₂ n⌉ + n`. -/
theorem spannerBound_le {n : ℕ} (h₀ : 1 ≤ n) :
    spannerBound n ≤ 2 * n * Nat.clog 2 n + n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, h₀ with
    | 1, _ => simp
    | n + 2, _ =>
      have ha := ih ((n + 3) / 2) (by omega) (by omega)
      have hb := ih ((n + 2) / 2) (by omega) (by omega)
      -- both halves have `⌈log₂⌉` at most `⌈log₂ n⌉ - 1`
      have hca : Nat.clog 2 ((n + 3) / 2) + 1 ≤ Nat.clog 2 (n + 2) := clog_half_le (by omega)
      have hcb : Nat.clog 2 ((n + 2) / 2) ≤ Nat.clog 2 ((n + 3) / 2) :=
        Nat.clog_mono_right 2 (by omega)
      have hab : (n + 3) / 2 + (n + 2) / 2 = n + 2 := by omega
      rw [spannerBound_add_two]
      nlinarith [Nat.mul_le_mul_left ((n + 3) / 2) hca, Nat.mul_le_mul_left ((n + 2) / 2) hcb,
        Nat.mul_le_mul_left ((n + 2) / 2) hca]

/-- The closed form is exact at powers of two, so it cannot be improved in general. -/
theorem spannerBound_two_pow (k : ℕ) :
    spannerBound (2 ^ k) = 2 * 2 ^ k * k + 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 < 2 ^ k := by positivity
    have heq : 2 ^ (k + 1) = (2 * 2 ^ k - 2) + 2 := by rw [pow_succ]; omega
    have ha : (2 * 2 ^ k - 2 + 3) / 2 = 2 ^ k := by omega
    have hb : (2 * 2 ^ k - 2 + 2) / 2 = 2 ^ k := by omega
    have key : spannerBound (2 ^ (k + 1)) = 2 * spannerBound (2 ^ k) + 2 * 2 ^ (k + 1) := by
      rw [heq, spannerBound_add_two, ha, hb, ← heq]
      ring
    rw [key, ih, pow_succ]
    ring

/-- The subproblem induced by a part `s' ⊆ s` of the source (SAND 2025, §4.1, split step): still
finite, simple, and a bi-clique on `s'`/`t`. -/
lemma induce_subproblem {H : Subgraph G} [Finite H.verts] {s t s' : Set V} (h₀ : H.IsSimple)
    (h₁ : H.IsBicliqueWith s t) (h₂ : s ∪ t ⊆ H.verts) (h₃ : s' ⊆ s) :
    Finite (H.induce (s' ∪ t)).verts ∧ (H.induce (s' ∪ t)).IsSimple ∧
      (H.induce (s' ∪ t)).IsBicliqueWith s' t := by
  have hsub : s' ∪ t ⊆ H.verts := (Set.union_subset_union_left t h₃).trans h₂
  have hle : H.induce (s' ∪ t) ≤ H := ⟨fun _ hv ↦ hsub hv, fun h ↦ h.2.2⟩
  exact ⟨finite_induce_verts H hsub, h₀.mono (toTemporalGraph_le hle), isBicliqueWith_induce h₁ h₃⟩

/-- The subproblem left by dismounting `x` (SAND 2025, §4.1, dismount step): still simple, a
bi-clique on `s`/`t \ {x}`, and `t \ {x}` is one vertex smaller than `t`. -/
lemma deleteVerts_subproblem {H : Subgraph G} {s t : Set V} {x : V} (h₀ : H.IsSimple)
    (h₁ : H.IsBicliqueWith s t) (h₂ : x ∈ t) (h₃ : x ∉ s) :
    (H.deleteVerts {x}).IsSimple ∧ (H.deleteVerts {x}).IsBicliqueWith s (t \ {x}) ∧
      (t \ {x}).ncard = t.ncard - 1 := by
  refine ⟨h₀.mono (toTemporalGraph_le deleteVerts_le), ?_, Set.ncard_sdiff_singleton_of_mem h₂⟩
  have h' := isBicliqueWith_deleteVerts (u := ({x} : Set V)) h₁
  rwa [Set.sdiff_singleton_eq_self h₃] at h'

/-- SAND 2025, §4.1 (dismount step): if `x` is one-sided dismountable in the bi-clique on `s`/`t`
and `H''` is a symmetric one-sided spanner of `H` without `x` from `s` to `t \ {x}`, then putting
`x` back with its two delegation edges yields a symmetric one-sided spanner of `H` from `s` to `t`,
with at most two more edges. -/
lemma isSpannerFromTo_of_dismount {H : Subgraph G} [G.IsSymm] [H.IsSymm] {s t : Set V} {x : V}
    (h₀ : H.IsBicliqueWith s t) (h₁ : H.OneSidedDismountable s t x)
    {H'' : Subgraph G} [H''.IsSymm] (h₂ : H''.IsSpannerFromTo (H.deleteVerts {x}) s (t \ {x})) :
    ∃ H' : Subgraph G, H'.IsSymm ∧ H'.IsSpannerFromTo H s t ∧
      H'.edgeSet.ncard ≤ H''.edgeSet.ncard + 2 := by
  obtain ⟨hx, x', hx', hne, y, hy, n, m, hlatest, hadj, hle⟩ := h₁
  have hxns : x ∉ s := Set.disjoint_right.mp h₀.isBipartiteWith.disjoint hx
  have hKbc : (H.deleteVerts {x}).IsBicliqueWith s (t \ {x}) := by
    have h' := isBicliqueWith_deleteVerts (u := ({x} : Set V)) h₀
    rwa [Set.sdiff_singleton_eq_self hxns] at h'
  have hx'mem : x' ∈ t \ {x} := ⟨hx', fun he ↦ hne (Set.mem_singleton_iff.mp he)⟩
  have hyne : y ≠ x' := fun he ↦ Set.disjoint_left.mp h₀.isBipartiteWith.disjoint hy (he ▸ hx')
  have hreach : (H.deleteVerts {x}).Reachable y x' := reachable_of_isBicliqueWith hKbc hy hx'mem
  obtain ⟨hyv, hx'v⟩ := mem_verts_of_reachable (h₂.2 y hy x' hx'mem hreach) hyne
  exact ⟨_, inferInstance, oneSidedDismountability h₀ hx hx' hne hlatest hadj hle h₂ hx'v hyv,
    ncard_edgeSet_oneSidedMount_le⟩

/-- SAND 2025, §4.1 (split step): symmetric one-sided spanners of the two source-halves `s₁`,
`s₂` combine, by union, into a symmetric one-sided spanner of `H` from `s₁ ∪ s₂` to `t`, with at
most `k₁ + k₂` edges. -/
lemma isSpannerFromTo_of_split {H H₁ H₂ : Subgraph G} {s t s₁ s₂ : Set V} [H₁.IsSymm] [H₂.IsSymm]
    (h₀ : H.IsBicliqueWith s t) (h₁ : s ∪ t ⊆ H.verts) (h₂ : s₁ ⊆ s) (h₃ : s₂ ⊆ s)
    (h₄ : H₁.IsSpannerFromTo (H.induce (s₁ ∪ t)) s₁ t)
    (h₅ : H₂.IsSpannerFromTo (H.induce (s₂ ∪ t)) s₂ t) :
    ∃ H' : Subgraph G, H'.IsSymm ∧ H'.IsSpannerFromTo H (s₁ ∪ s₂) t ∧
      H'.edgeSet.ncard ≤ H₁.edgeSet.ncard + H₂.edgeSet.ncard :=
  ⟨H₁ ⊔ H₂, inferInstance, isSpannerFromTo_sup_of_induce h₀ h₁ h₂ h₃ h₄ h₅,
    by rw [sup_edgeSet]; exact Set.ncard_union_le _ _⟩

/-- SAND 2025, §4.1 (strategy of Angrick et al.): a finite simple temporal bi-clique on a nonempty
source `s` and a target `t` at least as large admits a symmetric one-sided spanner from `s` to `t`
with at most `2 (|t| - |s|) + spannerBound |s|` edges: dismount `|t| - |s|` targets at two edges
each, then split the source in halves and recurse. -/
theorem exists_isSpannerFromTo_ncard_le {H : Subgraph G} [Finite H.verts] [G.IsSymm] [H.IsSymm]
    {s t : Set V} (h₀ : H.IsSimple) (h₁ : H.IsBicliqueWith s t) (h₂ : s.Nonempty)
    (h₃ : s.ncard ≤ t.ncard) :
    ∃ H' : Subgraph G, H'.IsSymm ∧ H'.IsSpannerFromTo H s t ∧
      H'.edgeSet.ncard ≤ 2 * (t.ncard - s.ncard) + spannerBound s.ncard := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · -- `t = ∅` forces `s.ncard = 0`; `⊥` is a (vacuous) one-sided spanner
    have hs0 : s.ncard = 0 := by simpa using h₃
    exact ⟨⊥, inferInstance, ⟨bot_le, fun x _ y hy _ ↦ hy.elim⟩, by simp [hs0]⟩
  induction hk : s.ncard + t.ncard using Nat.strong_induction_on generalizing H s t with
  | _ k ih =>
    have hsub : s ∪ t ⊆ H.verts := isBicliqueWith_subset_verts h₁ h₂ ht
    have hspos : 0 < s.ncard :=
      h₂.ncard_pos ((Set.toFinite H.verts).subset (Set.subset_union_left.trans hsub))
    -- recurse on a smaller part `s'` of the source, target `t` unchanged (split step, below)
    have hrec : ∀ s' ⊆ s, s'.Nonempty → s'.ncard < s.ncard →
        ∃ H' : Subgraph G, H'.IsSymm ∧ H'.IsSpannerFromTo (H.induce (s' ∪ t)) s' t ∧
          H'.edgeSet.ncard ≤ 2 * (t.ncard - s'.ncard) + spannerBound s'.ncard := by
      intro s' hs'sub hs'ne hs'lt
      obtain ⟨hfin, hsimple, hbc⟩ := induce_subproblem h₀ h₁ hsub hs'sub
      exact ih (s'.ncard + t.ncard) (by omega) hsimple hbc hs'ne (by omega) ht rfl
    rcases h₃.lt_or_eq with hlt | heq
    · -- SAND 2025, §4.1: dismount a target that delegates to another, through the pigeonhole
      obtain ⟨x, hdis⟩ := exists_oneSidedDismountable_of_ncard_lt h₀ h₁ h₂ hlt
      have hxns : x ∉ s := Set.disjoint_right.mp h₁.isBipartiteWith.disjoint hdis.1
      obtain ⟨hKsimple, hKbc, htx1⟩ := deleteVerts_subproblem h₀ h₁ hdis.1 hxns
      have htxNonempty : (t \ {x}).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨H'', hH''symm, hH''span, hH''bound⟩ :=
        ih (s.ncard + (t \ {x}).ncard) (by omega) hKsimple hKbc h₂ (by omega) htxNonempty rfl
      -- put `x` back with its two delegation edges (SAND 2025, §4.1, dismount step)
      obtain ⟨H', hH'symm, hH'span, hH'bound⟩ := isSpannerFromTo_of_dismount h₁ hdis hH''span
      exact ⟨H', hH'symm, hH'span, by omega⟩
    · -- `s.ncard = t.ncard`: split the source in two and recurse, or settle the base case
      rcases (by omega : s.ncard = 1 ∨ 2 ≤ s.ncard) with hone | htwo
      · -- base case: `s` and `t` are singletons joined by their one edge
        obtain ⟨a, hsa⟩ := Set.ncard_eq_one.mp hone
        obtain ⟨b, htb⟩ := Set.ncard_eq_one.mp (heq ▸ hone)
        obtain ⟨n', hadj⟩ := h₁.adj_of_mem (hsa ▸ rfl : a ∈ s) (htb ▸ rfl : b ∈ t)
        obtain ⟨H', hH'symm, hH'span, hH'card⟩ := exists_isSpannerFromTo_of_singleton hadj
        refine ⟨H', hH'symm, by rw [hsa, htb]; exact hH'span, ?_⟩
        grind only [spannerBound_one]
      · -- split step (SAND 2025, §4.1): halve `s`, dismount the other half of `t` in each piece
        obtain ⟨s₁, hs₁sub, hs₁card, hs₂card⟩ := exists_ncard_halves s
        set s₂ := s \ s₁ with hs₂def
        have hs1ne : s₁.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
        have hs2ne : s₂.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
        obtain ⟨H₁, hH₁symm, hH₁span, hH₁bound⟩ := hrec s₁ hs₁sub hs1ne (by omega)
        obtain ⟨H₂, hH₂symm, hH₂span, hH₂bound⟩ := hrec s₂ Set.sdiff_subset hs2ne (by omega)
        have hunion : s₁ ∪ s₂ = s := Set.union_sdiff_cancel hs₁sub
        -- halve the source and recombine the two sub-spanners by union (SAND 2025, §4.1, split)
        obtain ⟨H', hH'symm, hH'span, hH'bound⟩ :=
          isSpannerFromTo_of_split h₁ hsub hs₁sub (s₂ := s₂) Set.sdiff_subset hH₁span hH₂span
        refine ⟨H', hH'symm, hunion ▸ hH'span, ?_⟩
        obtain ⟨p, hp⟩ : ∃ p, s.ncard = p + 2 := ⟨s.ncard - 2, by omega⟩
        grind only [spannerBound_add_two]

/-- `f` bounds the one-sided spanners of temporal bi-cliques (Angrick et al.'s `𝒟(n) ≤ f n`, as
recalled in SAND 2025, §4.1): every finite simple temporal bi-clique with balanced nonempty parts
of size `n` admits a symmetric one-sided spanner from the source to the target with at most `f n`
edges. -/
def IsOneSidedSpannerBound (f : ℕ → ℕ) : Prop :=
  ∀ {V : Type u} {G : TemporalGraph V} {H : Subgraph G} [Finite H.verts] [G.IsSymm] [H.IsSymm]
    {s t : Set V}, H.IsSimple → H.IsBicliqueWith s t → s.Nonempty → s.ncard = t.ncard →
    ∃ H' : Subgraph G, H'.IsSymm ∧ H'.IsSpannerFromTo H s t ∧ H'.edgeSet.ncard ≤ f s.ncard

/-- A larger function is still a bound. -/
lemma IsOneSidedSpannerBound.mono {f g : ℕ → ℕ} (h₀ : IsOneSidedSpannerBound.{u} f)
    (h₁ : ∀ n, f n ≤ g n) : IsOneSidedSpannerBound.{u} g := by
  intro V G H _ _ _ s t h₂ h₃ h₄ h₅
  obtain ⟨H', hH'symm, hH'span, hH'bound⟩ := h₀ h₂ h₃ h₄ h₅
  exact ⟨H', hH'symm, hH'span, hH'bound.trans (h₁ s.ncard)⟩

/-- SAND 2025, §4.1: `spannerBound` bounds one-sided spanners. -/
theorem isOneSidedSpannerBound_spannerBound : IsOneSidedSpannerBound.{u} spannerBound := by
  intro V G H _ _ _ s t h₀ h₁ h₂ h₃
  obtain ⟨H', hH'symm, hH'span, hH'bound⟩ :=
    exists_isSpannerFromTo_ncard_le h₀ h₁ h₂ h₃.le
  exact ⟨H', hH'symm, hH'span, by omega⟩

section BigO

open Asymptotics Filter

/-- `⌈log₂ n⌉ ≤ log₂ n + 1`: `Nat.clog 2 n` is the ceiling of `Real.logb 2 n`
(`Real.natCeil_logb_natCast`), and a ceiling is less than its argument plus one. -/
private lemma clog_le_logb_add_one {n : ℕ} (hn : 1 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ Real.logb 2 n + 1 := by
  rw [← Real.natCeil_logb_natCast]
  exact (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) (by exact_mod_cast hn))).le

/-- `1 ≤ log₂ n` for `n ≥ 2`. -/
private lemma one_le_logb {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Real.logb 2 n := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  norm_num
  exact_mod_cast hn

/-- `spannerBound` is `O(n log n)`. -/
theorem spannerBound_isBigO :
    (fun n ↦ (spannerBound n : ℝ)) =O[atTop] fun n ↦ (n : ℝ) * Real.log n := by
  refine IsBigO.of_bound (5 / Real.log 2) (eventually_atTop.2 ⟨2, fun n hn ↦ ?_⟩)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    show 5 / Real.log 2 * (n * Real.log n) = 5 * (n * Real.logb 2 n) by
      rw [← Real.log_div_log]; ring]
  -- `spannerBound n ≤ 2 n ⌈log₂ n⌉ + n ≤ 2 n (log₂ n + 1) + n ≤ 5 n log₂ n`, since `1 ≤ log₂ n`
  have hb : (spannerBound n : ℝ) ≤ 2 * n * Nat.clog 2 n + n := by
    exact_mod_cast spannerBound_le (by omega)
  nlinarith [mul_le_mul_of_nonneg_left (clog_le_logb_add_one (by omega : 1 ≤ n))
      (by positivity : (0 : ℝ) ≤ 2 * n),
    le_mul_of_one_le_right (Nat.cast_nonneg n) (one_le_logb hn)]

/-- SAND 2025, §4.1 (Angrick et al.): temporal bi-cliques admit one-sided spanners of size
`O(n log n)`. -/
theorem exists_isBigO_isOneSidedSpannerBound :
    ∃ f : ℕ → ℕ, (fun n ↦ (f n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ) * Real.log n) ∧
      IsOneSidedSpannerBound.{u} f :=
  ⟨spannerBound, spannerBound_isBigO, isOneSidedSpannerBound_spannerBound⟩

end BigO

end Subgraph

end TemporalGraph
