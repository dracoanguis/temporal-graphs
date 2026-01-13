import TemporalGraph.NETemporalWalk

universe u

variable {V : Type u} {G : SimpleTemporalGraph V}

namespace SimpleTemporalGraph

/-- We define a Non-strict TemporalWalk, meaning multiple edges can be crossed at a given time. -/
inductive TemporalWalk : V → ℕ → V → ℕ → Type u
  | empty {u : V} {s : ℕ} : TemporalWalk u s u s
  | nonempty {u v : V} {s e : ℕ} (p : G.NETemporalWalk u s v e) : TemporalWalk u s v e
  deriving DecidableEq

def TemporalWalkSet (u v : V)
  : Set (Σ s t : ℕ, G.TemporalWalk u s v t) :=
  { p | ∃ (s t : ℕ), ∃ (tw : TemporalWalk u s v t), p = ⟨s, t, tw⟩ }

namespace TemporalWalk

/-- The length of a TemporalWalk is the number of edges along it. -/
def length {u v : V} {s t : ℕ} : G.TemporalWalk u s v t → ℕ
  | empty => 0
  | nonempty p => p.length

/-- The `support` of a TemporalWalk is the list of vertices it visits in order. -/
def support {u v : V} {s t : ℕ} : G.TemporalWalk u s v t → List V
  | @empty _ _ u _ => [u]
  | nonempty p => p.support

/-- The `darts` of a TemporalWalk is the list of darts (edge with a direction) it visits in
order. -/
def darts {u v : V} {s t : ℕ} : G.TemporalWalk u s v t → List (V × V × ℕ)
  | empty => []
  | nonempty p => p.darts

lemma time_mono {u v : V} {s e : ℕ} (tw : G.TemporalWalk u s v e) : s ≤ e
:= by
  cases tw with
  | empty => trivial
  | nonempty p => exact p.time_mono



end TemporalWalk

end SimpleTemporalGraph
