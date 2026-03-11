import TemporalGraph.Basic

universe u

namespace SimpleTemporalGraph

variable {V : Type u} {G : SimpleTemporalGraph V}

/-- This is a Nonempty Non-strict TemporalWalk. -/
inductive NonemptyTemporalWalk : V → ℕ → V → ℕ → Type u
  | Single {x y : V} {n : ℕ} (h: G.Adj x y n) : NonemptyTemporalWalk x n y n
  | Step {x y z : V} {n m k : ℕ}
    (h : G.Adj y z k)
    (p : NonemptyTemporalWalk x n y m)
    (h' : m ≤ k := by decide)
    : NonemptyTemporalWalk x n z k
  deriving DecidableEq

namespace NonemptyTemporalWalk

/-- The length of a NETemporalWalk is the number of edges along it. -/
def length {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → ℕ
  | Single _ => 1
  | Step _ p _ => 1 + p.length

/-- The `support` of a NETemporalWalk is the list of vertices it visits in order. -/
def support {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → List V
  | Single _ => y :: [x]
  | Step _ p _ => y :: p.support

/-- The `darts` of a NETemporalWalk is the list of darts (edge with a direction) it visits in
order. -/
def darts {x y : V} {n m : ℕ} : G.NonemptyTemporalWalk x n y m → List (V × V × ℕ)
  | @Single _ _ x y n _ => [⟨x ,⟨y, n⟩⟩]
  | @Step _ _ _ y z _ _ k _ p _ => ⟨y ,⟨ z, k⟩⟩ :: p.darts

def extend {x y z : V} {n m k l} (p : G.NonemptyTemporalWalk x n y m)
(ext : G.NonemptyTemporalWalk y k z l)
(h : m ≤ k := by decide)
: G.NonemptyTemporalWalk x n z l
:= match ext with
  | Single h_edge => Step h_edge p h
  | Step h_edge p' h_ord' => Step h_edge (extend p p' h) h_ord'

def prepend {x y z : V} {n m k : ℕ}
(h : G.Adj z x k)
(p : G.NonemptyTemporalWalk x n y m)
(h' : k ≤ n := by decide)
: G.NonemptyTemporalWalk z k y m
:= extend (Single h) p h'

lemma time_monotonicity {x y : V} {n m : ℕ} (tw : G.NonemptyTemporalWalk x n y m) : n ≤ m
:= by
  induction tw with
  | Single h => rfl
  | Step h p h' ih => exact le_trans ih h'

lemma EarliestEdge.time_bound_of_edge {x y z : V} {n m k : ℕ}
(tw : G.NonemptyTemporalWalk x n y m)
(h : G.EarliestEdge x z k)
: k ≤ n
:= by
  rw [EarliestEdge] at h
  induction tw with
  |Single h' => exact h.right _ _ h'
  |Step _ _ _ hi => exact hi

lemma LatestEdge.time_bound_of_edge {x y z : V} {n m k : ℕ}
(tw : G.NonemptyTemporalWalk x n y m)
(h : G.LatestEdge y z k)
: m ≤ k
:= by
  rw [LatestEdge] at h
  cases tw with
  | Single h' => exact h.right _ _ h'.symm
  | Step h' _ _ => exact h.right _ _ h'.symm


end NonemptyTemporalWalk

end SimpleTemporalGraph
