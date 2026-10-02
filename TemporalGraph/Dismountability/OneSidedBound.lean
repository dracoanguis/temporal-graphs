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
(`TemporalGraph/Dismountability/OneSided.lean`) by repeated halving, following SAND 2025, §4.1:
splitting the source part of a bi-clique into two halves of size `⌈n / 2⌉` and `⌊n / 2⌋`, then
dismounting the other half's targets at two edges each, yields the recurrence
`size(n) ≤ 2 * size(n / 2) + O(n)`. `spannerBound` is this recurrence made explicit (with the
`O(n)` term instantiated to `2 * n`), and `spannerBound_le` solves it in closed form,
`spannerBound n ≤ 2 * n * ⌈log₂ n⌉ + n`.

## Main definitions

* `TemporalGraph.Subgraph.spannerBound` : the SAND 2025, §4.1 recurrence on balanced one-sided
  instances.

## Main results

* `TemporalGraph.Subgraph.spannerBound_le` : closed form, `spannerBound n ≤ 2 n ⌈log₂ n⌉ + n`.
* `TemporalGraph.Subgraph.spannerBound_two_pow` : the bound is attained exactly at powers of two.
* `TemporalGraph.Subgraph.spannerBound_isBigO` : `spannerBound` is `O(n log n)`.

## References

* Carnevale, Casteigts & Corsini, *Dismountability in Temporal Cliques Revisited*, SAND 2025
  (LIPIcs 330, doi:10.4230/LIPIcs.SAND.2025.6), §4.1.
-/

open Asymptotics Filter

namespace TemporalGraph

namespace Subgraph

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
  suffices h : ∀ n, 1 ≤ n → spannerBound n ≤ 2 * n * Nat.clog 2 n + n from h n h₀
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h₀
    match n, h₀ with
    | 0, h₀ => omega
    | 1, _ => simp [Nat.clog_one_right]
    | (n + 2), _ =>
      have hab : (n + 3) / 2 + (n + 2) / 2 = n + 2 := by omega
      have ha_lt : (n + 3) / 2 < n + 2 := by omega
      have hb_lt : (n + 2) / 2 < n + 2 := by omega
      have ha_pos : 1 ≤ (n + 3) / 2 := by omega
      have hb_pos : 1 ≤ (n + 2) / 2 := by omega
      have hbound_a := ih _ ha_lt ha_pos
      have hbound_b := ih _ hb_lt hb_pos
      have hca : Nat.clog 2 ((n + 3) / 2) + 1 ≤ Nat.clog 2 (n + 2) := clog_half_le (by omega)
      have hmono : Nat.clog 2 ((n + 2) / 2) ≤ Nat.clog 2 ((n + 3) / 2) :=
        Nat.clog_mono_right 2 (by omega)
      have hcb : Nat.clog 2 ((n + 2) / 2) + 1 ≤ Nat.clog 2 (n + 2) := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 1 ≤ Nat.clog 2 (n + 2) from by omega)
      have hca' : Nat.clog 2 ((n + 3) / 2) ≤ k := by omega
      have hcb' : Nat.clog 2 ((n + 2) / 2) ≤ k := by omega
      have hma : 2 * ((n + 3) / 2) * Nat.clog 2 ((n + 3) / 2) ≤ 2 * ((n + 3) / 2) * k :=
        Nat.mul_le_mul le_rfl hca'
      have hmb : 2 * ((n + 2) / 2) * Nat.clog 2 ((n + 2) / 2) ≤ 2 * ((n + 2) / 2) * k :=
        Nat.mul_le_mul le_rfl hcb'
      have hdist : 2 * ((n + 3) / 2) * k + 2 * ((n + 2) / 2) * k = 2 * (n + 2) * k := by
        have hring : 2 * ((n + 3) / 2) * k + 2 * ((n + 2) / 2) * k =
            2 * ((n + 3) / 2 + (n + 2) / 2) * k := by ring
        rw [hring, hab]
      have htarget : 2 * (n + 2) * Nat.clog 2 (n + 2) = 2 * (n + 2) * k + 2 * (n + 2) := by
        rw [hk]; ring
      rw [spannerBound_add_two]
      omega

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

/-- `Nat.clog 2 n` is within `1` of `log₂ n`, for `n ≥ 2`: `⌈log₂ n⌉` is `Nat.clog 2 n` (cast via
`Real.natCeil_logb_natCast`), and a ceiling is below its argument plus one. -/
private lemma clog_le_log_div_log_two {n : ℕ} (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
  have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnonneg : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) hx
  have hceil : (⌈Real.logb 2 (n : ℝ)⌉₊ : ℝ) < Real.logb 2 (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one hnonneg
  have heq : Nat.clog 2 n = ⌈Real.logb 2 (n : ℝ)⌉₊ := (Real.natCeil_logb_natCast 2 n).symm
  rw [heq]
  exact hceil.le

/-- For `n ≥ 2`, `log₂ n ≥ 1`: monotonicity of `log` from `2 ≤ n`. -/
private lemma one_le_log_div_log_two {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ Real.log n / Real.log 2 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hle : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [one_le_div h2]
  exact Real.log_le_log (by norm_num) hle

/-- `spannerBound` is `O(n log n)`: by `spannerBound_le` and `⌈log₂ n⌉ ≤ log₂ n + 1`. -/
theorem spannerBound_isBigO :
    (fun n ↦ (spannerBound n : ℝ)) =O[atTop] fun n ↦ (n : ℝ) * Real.log n := by
  refine Asymptotics.IsBigO.of_bound (5 / Real.log 2)
    (Filter.eventually_atTop.2 ⟨2, fun n hn ↦ ?_⟩)
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (spannerBound n : ℝ)),
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * Real.log n)]
  -- the nat recurrence bound, cast to `ℝ`
  have hnat : spannerBound n ≤ 2 * n * Nat.clog 2 n + n := spannerBound_le (by omega)
  have hcast : (spannerBound n : ℝ) ≤ 2 * (n : ℝ) * (Nat.clog 2 n : ℝ) + (n : ℝ) := by
    exact_mod_cast hnat
  -- `Nat.clog 2 n ≤ log₂ n + 1`, scaled by the nonnegative factor `2 n`
  have hclog : (Nat.clog 2 n : ℝ) ≤ Real.log n / Real.log 2 + 1 := clog_le_log_div_log_two hn
  have hone : 1 ≤ Real.log n / Real.log 2 := one_le_log_div_log_two hn
  have e1 : 2 * (n : ℝ) * (Nat.clog 2 n : ℝ) ≤ 2 * (n : ℝ) * (Real.log n / Real.log 2 + 1) :=
    mul_le_mul_of_nonneg_left hclog (by positivity)
  -- the remaining `n` term absorbs into `n log₂ n`, since `log₂ n ≥ 1`
  have e2 : (n : ℝ) ≤ (n : ℝ) * (Real.log n / Real.log 2) := by
    calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
    _ ≤ (n : ℝ) * (Real.log n / Real.log 2) := mul_le_mul_of_nonneg_left hone hnR
  have hfinal :
      2 * (n : ℝ) * (Nat.clog 2 n : ℝ) + (n : ℝ) ≤ 5 / Real.log 2 * ((n : ℝ) * Real.log n) := by
    have hrw : 5 / Real.log 2 * ((n : ℝ) * Real.log n)
        = 5 * ((n : ℝ) * (Real.log n / Real.log 2)) := by ring
    rw [hrw]
    nlinarith [e1, e2]
  linarith [hcast, hfinal]

end Subgraph

end TemporalGraph
