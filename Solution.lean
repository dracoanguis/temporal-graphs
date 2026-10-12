/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Dismountability.CliqueSpanner

/-!
# Proved solution

Comparator matches the identically named declarations of `Challenge.lean`. The compared
definitions (`IsLocallyInjective`, `Journey`, `IsTemporalSpanner`) live in
`TemporalGraph.Dismountability.CliqueSpanner`, where `Challenge.lean` repeats them verbatim
(`Challenge.lean` does not import the library). The proofs bridge the labelling to the library's
`exists_isSpannerOf_ncard_le` and `exists_isBigO_isSpannerOf` (SAND 2025, §4.1).
-/

@[expose] public section

namespace TemporalCliqueSpanners

/-- Explicit bound: every temporal clique on `n` vertices admits a temporal spanner with at most
`2 n ⌈log₂ n⌉ + 4 n` edges. -/
theorem exists_isTemporalSpanner_card_le (V : Type) [Finite V] (lab : Sym2 V → ℕ)
    (h : IsLocallyInjective lab) :
    ∃ S : Finset (Sym2 V), IsTemporalSpanner S lab ∧
      S.card ≤ 2 * Nat.card V * Nat.clog 2 (Nat.card V) + 4 * Nat.card V :=
  isTemporalSpanner_card_le V lab h

open Asymptotics Filter in
/-- Casteigts–Peters–Schoeters (ICALP 2019), reproved by Carnevale–Casteigts–Corsini (SAND 2025,
§4.1): temporal cliques on `n` vertices admit temporal spanners of size `O(n log n)`. The bound
`f` is chosen once, uniformly over all temporal cliques. -/
theorem exists_isBigO_isTemporalSpanner :
    ∃ f : ℕ → ℕ, (fun n ↦ (f n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ) * Real.log n) ∧
      ∀ (V : Type) [Finite V] (lab : Sym2 V → ℕ), IsLocallyInjective lab →
        ∃ S : Finset (Sym2 V), IsTemporalSpanner S lab ∧ S.card ≤ f (Nat.card V) :=
  isTemporalSpanner_isBigO

end TemporalCliqueSpanners
