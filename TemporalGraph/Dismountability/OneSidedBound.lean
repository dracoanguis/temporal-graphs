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
`O(n)` term instantiated to `2 * n`), and `spannerBound_le` solves it in closed form,
`spannerBound n ≤ 2 * n * ⌈log₂ n⌉ + n`.

## Main definitions

* `TemporalGraph.Subgraph.spannerBound` : the SAND 2025, §4.1 recurrence on balanced one-sided
  instances.

## Main results

* `TemporalGraph.Subgraph.exists_isSpannerFromTo_of_singleton` : the base case of the recursion,
  a single edge is a one-sided spanner of itself.
* `TemporalGraph.Subgraph.spannerBound_le` : closed form, `spannerBound n ≤ 2 n ⌈log₂ n⌉ + n`.
* `TemporalGraph.Subgraph.spannerBound_two_pow` : the bound is attained exactly at powers of two.
* `TemporalGraph.Subgraph.spannerBound_isBigO` : `spannerBound` is `O(n log n)`.

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

end BigO

end Subgraph

end TemporalGraph
