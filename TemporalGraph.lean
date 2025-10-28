import TemporalGraph.TimeWalk

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

def triangle.path : triangle.TimeWalk 0 1 0 :=
  TimeWalk.single (by simp [triangle])

def triangle.path' : triangle.TimeWalk 0 2 1 :=
  TimeWalk.step (by simp [triangle])
    <| triangle.path

def triangle.path'' : triangle.TimeWalk 0 0 2 :=
  TimeWalk.step (by simp [triangle])
    <| triangle.path'

def triangle.path2 : triangle.TimeWalk 0 2 1 :=
  let e : triangle.Adj 0 1 0 := by simp [triangle]
  TimeWalk.single (e)
    |> TimeWalk.step (by simp [triangle])

#eval triangle.path''.darts

#check triangle.Footprint
