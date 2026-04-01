import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1245: [5/6, 77/2, 44/35, 3/121, 10/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 2  0 -1 -1  1
 0  1  0  0 -2
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1245

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 chain: drain e by 2 per step, add 1 to b
theorem e_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e + 2 * k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R3+R1+R1 chain: per round (0,b,c+1,d+1,e) -> (0,b-2,c+2,d,e+1)
theorem r3r1r1_chain : ∀ k b c d e, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    step fm
    step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

-- R3+R2+R2 chain: per round (0,0,c+1,d+1,e) -> (0,0,c,d+2,e+3)
theorem r3r2r2_chain : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + k + 1, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 3))
    ring_nf; finish

-- Main transition: (0, 0, 0, d+2, 4*d+5) →⁺ (0, 0, 0, d+3, 4*d+9)
theorem main_trans (d : ℕ) :
    ⟨(0 : ℕ), 0, 0, d + 2, 4 * d + 5⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, d + 3, 4 * d + 9⟩ := by
  -- Phase 1: R4 (first step for ⊢⁺, then chain)
  rw [show 4 * d + 5 = (4 * d + 3) + 2 from by ring]
  apply step_stepStar_stepPlus (by simp [fm] : (⟨0, 0, 0, d + 2, (4 * d + 3) + 2⟩ : Q) [fm]⊢ ⟨0, 1, 0, d + 2, 4 * d + 3⟩)
  -- Remaining R4 steps: (0, 1, 0, d+2, 4d+3) →* (0, 2d+2, 0, d+2, 1)
  rw [show 4 * d + 3 = 1 + 2 * (2 * d + 1) from by ring]
  apply stepStar_trans (e_to_b (2 * d + 1) 1 (d + 2) 1)
  rw [show 1 + (2 * d + 1) = 2 * d + 2 from by ring]
  -- State: (0, 2d+2, 0, d+2, 1)
  -- Phase 2: R5
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  -- State: (1, 2d+2, 1, d+1, 1)
  -- Phase 3: R1
  rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring]
  step fm
  -- State: (0, 2d+1, 2, d+1, 1)
  -- Phase 4: R3+R1+R1 chain (d rounds)
  rw [show 2 * d + 1 = 1 + 2 * d from by ring,
      show d + 1 = 1 + d from by ring]
  apply stepStar_trans (r3r1r1_chain d 1 1 1 1)
  rw [show 1 + d + 1 = d + 2 from by ring,
      show 1 + d = d + 1 from by ring]
  -- State: (0, 1, d+2, 1, d+1)
  -- Phase 5: R3
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  -- State: (2, 1, d+1, 0, d+2)
  -- Phase 6: R1
  step fm
  -- State: (1, 0, d+2, 0, d+2)
  -- Phase 7: R2
  step fm
  -- Phase 8: R3+R2+R2 chain (d+2 rounds)
  rw [show d + 1 + 1 + 1 = d + 3 from by omega]
  rw [show d + 1 + 1 = 0 + (d + 2) from by omega]
  apply stepStar_trans (r3r2r2_chain (d + 2) 0 0 (d + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d + 2, 4 * d + 5⟩) 0
  intro d
  exists d + 1
  exact main_trans d

end Sz22_2003_unofficial_1245
