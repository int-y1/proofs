import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1235: [5/6, 7/2, 44/35, 3/11, 132/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  0
 2  0 -1 -1  1
 0  1  0  0 -1
 2  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1235

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: move e to b
theorem e_to_b : ∀ k, ∀ b d, ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    rw [show b + 1 + k = b + (k + 1) from by ring]
    finish

-- R1R1R3 chain: k rounds
theorem r1r1r3_chain : ∀ k, ∀ b c d e, ⟨(2 : ℕ), b + 2 * k, c, d + k, e⟩ [fm]⊢* ⟨(2 : ℕ), b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    step fm; step fm; step fm
    rw [show c + k + 1 = c + (k + 1) from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

-- R3R2R2 chain: k rounds
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) d e)
    step fm; step fm; step fm
    rw [show d + k + 1 + 1 = d + (k + 1) + 1 from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

-- Main transition: (0, 0, 0, n+1, 2*n) ->+ (0, 0, 0, n+2, 2*n+2)
theorem main_transition (n : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, n + 1, 2 * n⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, n + 2, 2 * n + 2⟩ := by
  -- Phase 1: R4 chain, move e=2n to b
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n) 0 (n + 1))
  rw [show (0 : ℕ) + 2 * n = 2 * n from by ring]
  -- State: (0, 2n, 0, n+1, 0)
  -- Phase 2: R5
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 2 * n, 0, n + 1, 0⟩ : Q) [fm]⊢ ⟨2, 2 * n + 1, 0, n, 1⟩)
  -- State: (2, 2n+1, 0, n, 1)
  -- Phase 3: R1R1R3 chain, n rounds
  have h3 := r1r1r3_chain n 1 0 0 1
  rw [show 1 + 2 * n = 2 * n + 1 from by ring,
      show 0 + n = n from by ring,
      show 1 + n = n + 1 from by ring] at h3
  apply stepStar_trans h3
  -- State: (2, 1, n, 0, n+1)
  -- Phase 4: R1
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨2, 1, n, 0, n + 1⟩ : Q) [fm]⊢ ⟨1, 0, n + 1, 0, n + 1⟩))
  -- Phase 5: R2
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, 0, n + 1, 0, n + 1⟩ : Q) [fm]⊢ ⟨0, 0, n + 1, 1, n + 1⟩))
  -- State: (0, 0, n+1, 1, n+1)
  -- Phase 6: R3R2R2 chain, n+1 rounds
  have h6 := r3r2r2_chain (n + 1) 0 0 (n + 1)
  rw [show 0 + (n + 1) = n + 1 from by ring,
      show 0 + 1 = 1 from by ring,
      show n + 1 + 1 = n + 2 from by ring,
      show n + 1 + (n + 1) = 2 * n + 2 from by ring] at h6
  apply stepStar_trans h6
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 1, 2 * n⟩) 0
  intro n
  exists n + 1
  exact main_transition n

end Sz22_2003_unofficial_1235
