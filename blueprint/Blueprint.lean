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

{include 0 Blueprint.Chapters.Model}
{include 0 Blueprint.Chapters.Walks}
{include 0 Blueprint.Chapters.Spanners}
{include 0 Blueprint.Chapters.Dismountability}
{include 0 Blueprint.Chapters.MainTheorem}
{include 0 Blueprint.Chapters.LinearSpanners}

{blueprint_graph}

{blueprint_summary}
