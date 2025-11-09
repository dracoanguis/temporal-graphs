
import TemporalGraph.Basic

universe u

variable {V : Type u}
variable {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph

/-- We define a Non-strict TimeWalk, meaning multiple edges can be crossed at a given time. -/
inductive TimeWalk : V → ℕ → V → ℕ → Type u
  | single {u v : V} {s : ℕ} (h: G.Adj u v s) : TimeWalk u s v s
  | step {u v w : V} {s t t' : ℕ}
    (h : G.Adj v w t')
    (p : TimeWalk u s v t)
    (h' : t ≤ t' := by decide)
    : TimeWalk u s w t'
  deriving DecidableEq

namespace TimeWalk

/-- The length of a TimeWalk is the number of edges along it. -/
def length {u v : V} {s t : ℕ} : G.TimeWalk u s v t → ℕ
  | single _ => 1
  | step _ p _ => 1 + p.length

/-- The `support` of a TimeWalk is the list of vertices it visits in order. -/
def support {u v : V} {s t : ℕ} : G.TimeWalk u s v t → List V
  | single _ => v :: [u]
  | step _ p _ => v :: p.support

/-- The `darts` of a TimeWalk is the list of darts (edge with a direction) it visits in order. -/
def darts {u v : V} {s t : ℕ} : G.TimeWalk u s v t → List (V × V × ℕ)
  | @single _ _ u v t _ => [⟨u ,⟨v, t⟩⟩]
  | @step _ _ _ v w _ _ t' _ p _ => ⟨v ,⟨ w, t'⟩⟩ :: p.darts



end TimeWalk

end SimpleTemporalGraph
