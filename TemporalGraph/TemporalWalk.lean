import TemporalGraph.Basic

universe u

variable {V : Type u}
variable {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph

/-- We define a Non-strict TemporalWalk, meaning multiple edges can be crossed at a given time. -/
inductive TemporalWalk : V → ℕ → V → ℕ → Type u
  | single {u v : V} {s : ℕ} (h: G.Adj u v s) : TemporalWalk u s v s
  | step {u v w : V} {s t t' : ℕ}
    (h : G.Adj v w t')
    (p : TemporalWalk u s v t)
    (h' : t ≤ t' := by decide)
    : TemporalWalk u s w t'
  deriving DecidableEq

def TemporalWalkSet (u v : V)
  : Set (Σ s t : ℕ, G.TemporalWalk u s v t) :=
  { p | ∃ (s t : ℕ), ∃ (tw : TemporalWalk u s v t), p = ⟨s, t, tw⟩ }

namespace TemporalWalk

/-- The length of a TemporalWalk is the number of edges along it. -/
def length {u v : V} {s t : ℕ} : G.TemporalWalk u s v t → ℕ
  | single _ => 1
  | step _ p _ => 1 + p.length

/-- The `support` of a TemporalWalk is the list of vertices it visits in order. -/
def support {u v : V} {s t : ℕ} : G.TemporalWalk u s v t → List V
  | single _ => v :: [u]
  | step _ p _ => v :: p.support

/-- The `darts` of a TemporalWalk is the list of darts (edge with a direction) it visits in
order. -/
def darts {u v : V} {s t : ℕ} : G.TemporalWalk u s v t → List (V × V × ℕ)
  | @single _ _ u v t _ => [⟨u ,⟨v, t⟩⟩]
  | @step _ _ _ v w _ _ t' _ p _ => ⟨v ,⟨ w, t'⟩⟩ :: p.darts

def extend {u v v' : V} {s t s' t'} (p : G.TemporalWalk u s v t) (ext : G.TemporalWalk v s' v' t')
  (h_ord : t ≤ s' := by decide)
  : G.TemporalWalk u s v' t'
  := match ext with
  | single h_edge => step h_edge p h_ord
  | step h_edge p' h_ord' => step h_edge (extend p p' h_ord) h_ord'

def prepend {u v u' : V} {s t s' : ℕ}
  (h : G.Adj u' u s')
  (p : G.TemporalWalk u s v t)
  (h' : s' ≤ s := by decide)
  : G.TemporalWalk u' s' v t
  := extend (single h) p h'


end TemporalWalk

end SimpleTemporalGraph
