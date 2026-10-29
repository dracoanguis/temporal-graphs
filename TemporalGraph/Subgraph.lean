/-
Copyright (c) 2026 Ethan Bargaud-Arm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Bargaud-Arm
-/
module

public import TemporalGraph.Subgraph.Basic
public import TemporalGraph.Subgraph.Operations
public import TemporalGraph.Subgraph.EdgeSet

/-!
# Sub-temporal-graphs

Aggregator for the subgraph API:

* `TemporalGraph.Subgraph.Basic` : the structure, its bounded order, `induce`, `deleteVerts`,
  `addVerts`.
* `TemporalGraph.Subgraph.Operations` : `addArc`, `addEdge`, earliest and latest edges, neighbor
  sets.
* `TemporalGraph.Subgraph.EdgeSet` : edge sets, sizes, `toSubgraph`, `Subgraph.fromEdgeSet`.
-/
