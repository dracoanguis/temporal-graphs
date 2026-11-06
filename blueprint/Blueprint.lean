import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Blueprint.TeXPrelude
import Blueprint.Chapters.Model
import Blueprint.Chapters.Walks
import Blueprint.Chapters.Spanners
import Blueprint.Chapters.Dismountability
import Blueprint.Chapters.MainTheorem
import Blueprint.Chapters.LinearSpanners

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Temporal Graphs" =>

%%%
authors := ["Ethan Bargaud-Arm"]
%%%

This blueprint describes `temporal-graphs`, a Lean 4 and Mathlib library on temporal graphs:
graphs whose edges carry discrete times, where a walk must follow non-decreasing times.

*State of the formalization.* Every statement below is formalized and proved: the progress
summary at the end is computed from the Lean declarations, not maintained by hand. The library
proves that every finite, simple, proper temporal clique on $`n` vertices admits a temporal
spanner

* with $`O(n \log n)` edges, explicitly $`2n\lceil\log_2 n\rceil + 4n`, following Carnevale,
  Casteigts and Corsini (SAND 2025);
* with at most $`7n` edges, following Baligács (arXiv:2606.05156v1, 2026), which answers the
  question of Casteigts, Peters and Schoeters (ICALP 2019 / JCSS 2021).

Both bounds are instances of one generic clique induction, which handles the dismountable case
once; the linear bound reuses it unchanged, together with SAND's structure of non-dismountable
cliques. {ref "chap:main-theorem"}[Main results] explains this proof engine and what is specific
to each bound.

*Not formalized.* The reductions of both papers to simple and proper cliques (these properties
are hypotheses here); Baligács's Lemma 4, Lemma 10 and Proposition 11; and the polynomial
running time of the constructions.

*Chapters.* {ref "chap:model"}[Temporal graphs], {ref "chap:walks"}[Walks and reachability] and
{ref "chap:spanners"}[Sub-temporal-graphs and spanners] set up the model;
{ref "chap:dismountability"}[Dismountability] follows SAND 2025 and contains the clique
induction; {ref "chap:main-theorem"}[Main results] states the two bounds;
{ref "chap:linear-spanners"}[Linear spanners] follows Baligács.

{include 0 Blueprint.Chapters.Model}
{include 0 Blueprint.Chapters.Walks}
{include 0 Blueprint.Chapters.Spanners}
{include 0 Blueprint.Chapters.Dismountability}
{include 0 Blueprint.Chapters.MainTheorem}
{include 0 Blueprint.Chapters.LinearSpanners}

{blueprint_graph}

{blueprint_summary}
