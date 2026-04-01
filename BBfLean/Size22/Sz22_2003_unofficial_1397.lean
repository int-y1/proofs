import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1397: [7/15, 1/14, 99/7, 4/33, 175/2]

Vector representation:
```
 0 -1 -1  1  0
-1  0  0 -1  0
 0  2  0 -1  1
 2 -1  0  0 -1
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1397

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

-- R3,R1,R1 chain: each round c decreases by 2, d and e increase by 1.
theorem r3r1r1_chain : ∀ k c d e, ⟨0, 0, c + 2 * k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih c (d + 1) (e + 1)); ring_nf; finish

-- R3 chain with c=0: d drains to e, b grows by 2 per step.
theorem r3_chain : ∀ k b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 2) (e + 1)); ring_nf; finish

-- R4 chain: b and e drain together, a grows by 2 per step.
theorem r4_chain : ∀ k a, ⟨a, k + 1, 0, 0, k⟩ [fm]⊢* ⟨a + 2 * k, 1, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · rw [show k + 1 + 1 = (k + 1) + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2)); ring_nf; finish

-- R2,R5 chain: from (2k, 0, c, 1, 0), each round: R2 then R5.
theorem r2r5_chain : ∀ k c, ⟨2 * k, 0, c, 1, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 2)); ring_nf; finish

-- All phases after R3,R1,R1 chain: (0, 0, 1, n+1, n) ⊢⁺ (0, 0, 4n+3, 1, 0)
theorem phases_tail (n : ℕ) :
    ⟨0, 0, 1, n + 1, n⟩ [fm]⊢⁺ ⟨0, 0, 4 * n + 3, 1, 0⟩ := by
  -- R3: (0, 2, 1, n, n+1). This is the ⊢⁺ step.
  step fm
  -- R1: (0, 1, 0, n+1, n+1)
  step fm
  -- R3 chain: (0, 1, 0, n+1, n+1) ⊢* (0, 2n+3, 0, 0, 2n+2)
  apply stepStar_trans (r3_chain (n + 1) 1 (n + 1))
  rw [show 1 + 2 * (n + 1) = (2 * n + 2) + 1 from by ring,
      show n + 1 + (n + 1) = 2 * n + 2 from by ring]
  -- R4 chain: (0, (2n+2)+1, 0, 0, 2n+2) ⊢* (4n+4, 1, 0, 0, 0)
  apply stepStar_trans (r4_chain (2 * n + 2) 0)
  rw [show 0 + 2 * (2 * n + 2) = 4 * n + 4 from by ring]
  -- R5, R1, R2, R2: (4n+4, 1, 0, 0, 0) -> (4n+1, 0, 1, 0, 0)
  step fm; step fm; step fm; step fm
  -- R5: (4n, 0, 3, 1, 0)
  step fm
  -- R2,R5 chain: (4n, 0, 3, 1, 0) ⊢* (0, 0, 4n+3, 1, 0)
  rw [show 4 * n = 2 * (2 * n) from by ring]
  apply stepStar_trans (r2r5_chain (2 * n) 3)
  ring_nf; finish

-- Main transition: (0, 0, 2n+1, 1, 0) ⊢⁺ (0, 0, 4n+3, 1, 0)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 2 * n + 1, 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 4 * n + 3, 1, 0⟩ := by
  rw [show 2 * n + 1 = 1 + 2 * n from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_stepPlus_stepPlus (r3r1r1_chain n 1 0 0)
  rw [show 0 + n + 1 = n + 1 from by ring, show 0 + n = n from by ring]
  exact phases_tail n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 1, 0⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n + 1, 1, 0⟩) 2
  intro n
  exact ⟨2 * n + 1, by
    rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_1397
