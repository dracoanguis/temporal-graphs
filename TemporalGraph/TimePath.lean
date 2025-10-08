
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


/- inductive TimePath (G : SimpleTemporalGraph V) : Type u
  | single {v₁ v₂ : V} {t : ℕ} (edge : G.Adj v₁ v₂ t) : TimePath G
  | cons {v₁ v₂ v₃ : V} {t₁ t₂ : ℕ}
    (edge : G.Adj v₂ v₃ t₂)
    (prev : TimePath G)
    (h : match prev with
      | single (_ _ u t) => (u = v₂) ∧ (t < t₂)
      | cons (_ _ u t) _ => (u = v₂) ∧ (t < t₂)
    )
-/

namespace TimePath

--def lastVertex {V} {G : SimpleTemporalGraph V} :
--    ∀ {n}, TimePath G n → V
--  | _, single v _ => v
--  | _, step prev _ => _root_.id prev.lastVertex
--
--def lastTime {V} {G : SimpleTemporalGraph V} :
--    ∀ {n}, TimePath G n → Nat
--  | _, single _ t => t
--  | _, step _ _ _ t₁ _ _ _ _ => t₁

end TimePath

end SimpleTemporalGraph
