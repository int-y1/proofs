import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #923: [4/15, 33/14, 1375/2, 7/11, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  3  0  1
 0  0  0  1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_923

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase: R1/R2 interleaved chain
-- From (a, 1, c+d+1, d, e) to (a+d, 1, c+1, 0, e+d)
theorem r1r2_chain : ∀ d, ∀ a c e,
    ⟨a, 1, c + d + 1, d, e⟩ [fm]⊢* ⟨a + d, 1, c + 1, 0, e + d⟩ := by
  intro d; induction' d with d ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (d + 1) + 1 = (c + d + 1) + 1 from by ring,
        show (d : ℕ) + 1 = d + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

-- Phase: R3 drain (consumes a, adds 3 to c and 1 to e per step)
-- From (k, 0, c, 0, e) to (0, 0, c+3*k, 0, e+k)
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 3) (e + 1)); ring_nf; finish

-- Phase: R4 drain (transfers e to d)
-- From (0, 0, c, d, k) to (0, 0, c, d+k, 0)
theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

-- Main transition: (0, 0, c+e+2, 0, e+1) ⊢⁺ (0, 0, c+3*e+7, 0, 2*e+2)
-- Phases: R4 drain, R5 kick, R1/R2 chain, final R1, R3 drain
theorem main_trans (c e : ℕ) :
    ⟨0, 0, c + e + 2, 0, e + 1⟩ [fm]⊢⁺
    ⟨0, 0, c + 3 * e + 7, 0, 2 * e + 2⟩ := by
  -- Phase 1: R4 drain: (0,0,c+e+2,0,e+1) ⊢* (0,0,c+e+2,e+1,0)
  have h1 : ⟨0, 0, c + e + 2, 0, e + 1⟩ [fm]⊢*
      ⟨0, 0, c + e + 2, e + 1, 0⟩ := by
    have := r4_drain (e + 1) (c + e + 2) 0
    rw [show 0 + (e + 1) = e + 1 from by ring] at this
    exact this
  -- Phase 2: R5 kick: (0,0,c+e+2,e+1,0) → (0,1,c+e+2,e,0)
  have h2 : ⟨0, 0, c + e + 2, e + 1, 0⟩ [fm]⊢⁺
      ⟨0, 1, c + e + 2, e, 0⟩ := by
    apply step_stepPlus
    show fm ⟨0, 0, c + e + 2, e + 1, 0⟩ = some ⟨0, 1, c + e + 2, e, 0⟩
    unfold fm; simp only
  -- Phase 3: R1/R2 chain: (0,1,c+e+2,e,0) ⊢* (e,1,c+2,0,e)
  have h3 : ⟨0, 1, c + e + 2, e, 0⟩ [fm]⊢*
      ⟨e, 1, c + 2, 0, e⟩ := by
    have := r1r2_chain e 0 (c + 1) 0
    rw [show (c + 1) + e + 1 = c + e + 2 from by ring,
        show (c + 1) + 1 = c + 2 from by ring] at this
    ring_nf at this ⊢; exact this
  -- Phase 4: Final R1: (e,1,c+2,0,e) → (e+2,0,c+1,0,e)
  have h4 : ⟨e, 1, c + 2, 0, e⟩ [fm]⊢*
      ⟨e + 2, 0, c + 1, 0, e⟩ := by
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply step_stepStar
    show fm ⟨e, 1, (c + 1) + 1, 0, e⟩ = some ⟨e + 2, 0, c + 1, 0, e⟩
    unfold fm; simp only
  -- Phase 5: R3 drain: (e+2,0,c+1,0,e) ⊢* (0,0,c+1+3*(e+2),0,e+(e+2))
  have h5 : ⟨e + 2, 0, c + 1, 0, e⟩ [fm]⊢*
      ⟨0, 0, c + 3 * e + 7, 0, 2 * e + 2⟩ := by
    have := r3_drain (e + 2) (c + 1) e
    rw [show (c + 1) + 3 * (e + 2) = c + 3 * e + 7 from by ring,
        show e + (e + 2) = 2 * e + 2 from by ring] at this
    exact this
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 1⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, e⟩ ↦ ⟨0, 0, c + e + 2, 0, e + 1⟩) ⟨1, 0⟩
  intro ⟨c, e⟩
  refine ⟨⟨c + e + 4, 2 * e + 1⟩, ?_⟩
  show ⟨0, 0, c + e + 2, 0, e + 1⟩ [fm]⊢⁺
    ⟨0, 0, (c + e + 4) + (2 * e + 1) + 2, 0, (2 * e + 1) + 1⟩
  rw [show (c + e + 4) + (2 * e + 1) + 2 = c + 3 * e + 7 from by ring,
      show (2 * e + 1) + 1 = 2 * e + 2 from by ring]
  exact main_trans c e

end Sz22_2003_unofficial_923
