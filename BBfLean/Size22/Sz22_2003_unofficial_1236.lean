import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1236: [5/6, 7/2, 44/35, 3/11, 484/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  0
 2  0 -1 -1  1
 0  1  0  0 -1
 2  0  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1236

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | _ => none

-- R4 chain: drain e to b
theorem e_to_b : ∀ k b d e, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R3+R1+R1 chain: k rounds
theorem r3r1r1_chain : ∀ k b c d e,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + k + 1, d, e + k⟩ := by
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

-- R3+R2+R2 chain: k rounds
theorem r3r2r2_chain : ∀ k c d e,
    ⟨(0 : ℕ), (0 : ℕ), c + k, d + 1, e⟩ [fm]⊢*
    ⟨(0 : ℕ), (0 : ℕ), c, d + 1 + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih c (d + 1) (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, n+2, 2n+2) →⁺ (0, 0, 0, n+3, 2n+4)
theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, n + 2, 2 * n + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, n + 3, 2 * n + 4⟩ := by
  -- Phase 1: R4 x (2n+2): drain e to b
  rw [show (2 * n + 2 : ℕ) = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n + 2) 0 (n + 2) 0)
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring]
  -- State: (0, 2n+2, 0, n+2, 0)
  -- Phase 2: R5
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 2 * n + 2, 0, (n + 1) + 1, 0⟩ : Q) [fm]⊢ ⟨2, 2 * n + 2, 0, n + 1, 2⟩)
  -- State: (2, 2n+2, 0, n+1, 2)
  -- Phase 3: R1 x 2
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
  step fm
  -- State: (0, 2n, 2, n+1, 2)
  -- Phase 4: R3+R1+R1 x n rounds
  rw [show 2 * n = 0 + 2 * n from by ring,
      show n + 1 = 1 + n from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain n 0 1 1 2)
  rw [show 1 + n + 1 = n + 2 from by ring,
      show 2 + n = n + 2 from by ring]
  -- State: (0, 0, n+2, 1, n+2)
  -- Phase 5: R3
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- State: (2, 0, n+1, 0, n+3)
  -- Phase 6: R2 x 2
  step fm
  step fm
  -- State: (0, 0, n+1, 2, n+3)
  -- Phase 7: R3+R2+R2 x (n+1) rounds
  rw [show n + 1 + 1 + 1 = n + 3 from by ring,
      show 0 + 2 * n + 4 = 2 * n + 4 from by ring,
      show n + 1 = 0 + (n + 1) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (n + 1) 0 1 (n + 3))
  rw [show 1 + 1 + (n + 1) = n + 3 from by ring,
      show n + 3 + (n + 1) = 2 * n + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 2 * n + 2⟩) 0
  intro n
  exists n + 1
  rw [show (n + 1) + 2 = n + 3 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1236
