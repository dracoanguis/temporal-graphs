
import TemporalGraph.Basic

universe u

variable {V : Type u}
variable {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph

/-- We define a strict TimeWalk, meaning only one edge can be crossed at a given time. -/
inductive TimeWalk : V → V → ℕ → Type u
  | single {u v : V} {t : ℕ} (h: G.Adj u v t) : TimeWalk u v t
  | step {u v w : V} {t t' : ℕ} (h : G.Adj v w t')
    (p : TimeWalk u v t) (h' : t < t' := by decide)
    : TimeWalk u w t'
  deriving DecidableEq

namespace TimeWalk

/-- The length of a TimeWalk is the number of edges along it. -/
def length {u v : V} {t : ℕ} : G.TimeWalk u v t → ℕ
  | single _ => 1
  | step _ p _ => 1 + p.length

/-- The `support` of a TimeWalk is the list of vertices it visits in order. -/
def support {u v : V} {t : ℕ} : G.TimeWalk u v t → List V
  | single _ => v :: [u]
  | step _ p _ => v :: p.support

/-- The `darts` of a TimeWalk is the list of darts (edge with a direction) it visits in order. -/
def darts {u v : V} {t : ℕ} : G.TimeWalk u v t → List (V × V × ℕ)
  | @single _ _ u v t _ => [⟨u ,⟨ v, t⟩⟩]
  | @step _ _ _ v w _ t' _ p _ => ⟨v ,⟨ w, t'⟩⟩ :: p.darts


theorem subtempgraph_walk_is_graph_walk (G G' : SimpleTemporalGraph V) {u v : V}
: G' ≤ G → ∀ t : ℕ, (G'.TimeWalk u v t → G.TimeWalk u v t)
:= by
  intro h_sub t h_tw
  induction h_tw with
  | single h => exact (single (h_sub h))
  | step h _ h' h_i => exact (step (h_sub h) h_i h')

end TimeWalk

end SimpleTemporalGraph
