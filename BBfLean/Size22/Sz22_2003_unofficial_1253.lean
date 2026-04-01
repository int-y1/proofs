import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1253: [5/6, 77/2, 52/35, 3/13, 78/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  1  1  0
 2  0 -1 -1  0  1
 0  1  0  0  0 -1
 1  1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1253

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a+1, b+1, c, d, e, f+1⟩
  | _ => none

-- Phase 1: drain f to b (R4 repeated)
theorem f_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- Phase 4: R3-R1-R1 chain
-- Each round: (0,b+2,c+1,d+1,E,f) -> (0,b,c+2,d,E,f+1)
theorem r3r1r1_chain : ∀ k, ∀ b c d E f,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, E, f⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k + 1, d, E, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d E f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) E f)
    rw [show c + k + 1 = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    step fm
    step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring,
        show f + k + 1 = f + (k + 1) from by ring]
    finish

-- Phase 5: R3-R2-R2 chain
-- Each round: (0,0,c+1,d+1,e,f) -> (0,0,c,d+2,e+2,f+1)
theorem r3r2r2_chain : ∀ k, ∀ c d e f,
    ⟨(0 : ℕ), 0, c + k, d + 1, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + k + 1, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e f)
    rw [show (c + 1) = c + 1 from rfl,
        show d + k + 1 = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + k + 2 = d + (k + 1) + 1 from by ring,
        show e + 2 * k + 2 = e + 2 * (k + 1) from by ring,
        show f + k + 1 = f + (k + 1) from by ring]
    finish

-- Main transition: canonical(n) ->+ canonical(n+1)
-- canonical(n) = (0, 0, 0, n+2, n^2+2n+2, 2n+2)
theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, n + 2, n * n + 2 * n + 2, 2 * n + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, n + 3, n * n + 4 * n + 5, 2 * n + 4⟩ := by
  -- Phase 1: drain f to b
  rw [show (2 * n + 2 : ℕ) = (2 * n + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (f_to_b (2 * n + 1) 1 (n + 2) (n * n + 2 * n + 2))
  rw [show 1 + (2 * n + 1) = 2 * n + 2 from by ring]
  -- State: (0, 2n+2, 0, n+2, n^2+2n+2, 0)
  -- Phase 2: R5
  rw [show (n * n + 2 * n + 2 : ℕ) = (n * n + 2 * n + 1) + 1 from by ring]
  apply stepStar_trans (step_stepStar (by simp [fm] :
    (⟨0, 2 * n + 2, 0, n + 2, (n * n + 2 * n + 1) + 1, 0⟩ : Q) [fm]⊢
    ⟨1, 2 * n + 3, 0, n + 2, n * n + 2 * n + 1, 1⟩))
  -- Phase 3: R1
  apply stepStar_trans (step_stepStar (by simp [fm] :
    (⟨1, 2 * n + 3, 0, n + 2, n * n + 2 * n + 1, 1⟩ : Q) [fm]⊢
    ⟨0, 2 * n + 2, 1, n + 2, n * n + 2 * n + 1, 1⟩))
  -- State: (0, 2n+2, 1, n+2, n^2+2n+1, 1)
  -- Phase 4: R3-R1-R1 chain (n+1 rounds)
  rw [show (2 * n + 2 : ℕ) = 0 + 2 * (n + 1) from by ring,
      show (n + 2 : ℕ) = 1 + (n + 1) from by ring]
  apply stepStar_trans (r3r1r1_chain (n + 1) 0 0 1 (n * n + 2 * n + 1) 1)
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show 1 + (n + 1) = n + 2 from by ring]
  -- State: (0, 0, n+2, 1, n^2+2n+1, n+2)
  -- Phase 5: R3-R2-R2 chain (n+2 rounds)
  have h5 := r3r2r2_chain (n + 2) 0 0 (n * n + 2 * n + 1) (n + 2)
  rw [show 0 + (n + 2) = n + 2 from by ring,
      show 0 + 1 = 1 from by ring] at h5
  apply stepStar_trans h5
  rw [show n + 2 + 1 = n + 3 from by ring,
      show n * n + 2 * n + 1 + 2 * (n + 2) = n * n + 4 * n + 5 from by ring,
      show n + 2 + (n + 2) = 2 * n + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, n * n + 2 * n + 2, 2 * n + 2⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  rw [show (n + 1) * (n + 1) + 2 * (n + 1) + 2 = n * n + 4 * n + 5 from by ring,
      show (n + 1) + 2 = n + 3 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1253
