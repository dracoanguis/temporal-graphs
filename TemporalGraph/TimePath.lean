
import TemporalGraph.Basic

universe u

variable {V : Type u}
variable {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph


inductive TimePath : V → V → ℕ → Type u
  | single {u v : V} {t : ℕ} (h: G.Adj u v t) : TimePath u v t
  | step {u v w : V} {t t' : ℕ} (h : G.Adj v w t')
    (p : TimePath u v t) (h' : t < t' := by decide)
    : TimePath u w t'
  deriving DecidableEq

namespace TimePath

/-- The length of a TimePath is the number of edges along it. -/
def length {u v : V} {t : ℕ} : G.TimePath u v t → ℕ
  | single _ => 1
  | step _ p _ => 1 + p.length

/-- The `support` of a TimePath is the list of vertices it visits in order. -/
def support {u v : V} {t : ℕ} : G.TimePath u v t → List V
  | single _ => v :: [u]
  | step _ p _ => v :: p.support

/-- The `darts` of a TimePath is the list of darts (edge with a direction) it visits in order. -/
def darts {u v : V} {t : ℕ} : G.TimePath u v t → List (V × V × ℕ)
  | @single _ _ u v t _ => [⟨u ,⟨ v, t⟩⟩]
  | @step _ _ _ v w _ t' _ p _ => ⟨v ,⟨ w, t'⟩⟩ :: p.darts

end TimePath

end SimpleTemporalGraph
