import TemporalGraph.TemporalWalk
import TemporalGraph.SubTempGraph
import TemporalGraph.Connectivity.SubTempGraph
import TemporalGraph.Maps

open SimpleTemporalGraph

def triangle : SimpleTemporalGraph (Fin 3) :=
  { Adj := fun v w t =>
    match t with
    | 0 => (v=0 ∧ w=1) ∨ (w=0 ∧ v=1)
    | 1 => (v=1 ∧ w=2) ∨ (w=1 ∧ v=2)
    | 2 => (v=2 ∧ w=0) ∨ (w=2 ∧ v=0)
    | _ => False
    symm := by aesop_temporal_graph
    loopless := by aesop_temporal_graph
  }

def triangle.path : triangle.TemporalWalk 0 0 1 0 :=
  TemporalWalk.single (by simp [triangle])

def triangle.path' : triangle.TemporalWalk 0 0 2 1 :=
  TemporalWalk.step (by simp [triangle])
    <| triangle.path

def triangle.path'' : triangle.TemporalWalk 0 0 0 2 :=
  TemporalWalk.step (by simp [triangle])
    <| triangle.path'

def triangle.path2 : triangle.TemporalWalk 0 0 2 1 :=
  let e : triangle.Adj 0 1 0 := by simp [triangle]
  TemporalWalk.single (e)
    |> TemporalWalk.step (by simp [triangle])

#eval triangle.path''.darts

#check triangle.Footprint

example : triangle.IsProper
:= by
  unfold SimpleTemporalGraph.IsProper
  intro u
  admit -- way too long and useless

#check (triangle.induce ({u : Fin 3 | u ≠ 3})).Adj
