import TemporalGraph.Basic

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
