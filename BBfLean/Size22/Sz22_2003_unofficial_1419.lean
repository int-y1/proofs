import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1419: [7/15, 1331/3, 6/77, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0 -1  0  0  3
 1  1  0 -1 -1
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1419

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3+R2 chain: (a, 0, 0, D+k, E+1) →* (a+k, 0, 0, D, E+2k+1)
theorem r3r2_chain : ∀ k a D E, ⟨a, 0, 0, D + k, E + 1⟩ [fm]⊢* ⟨a + k, 0, 0, D, E + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a D E
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) D (E + 2))
    ring_nf; finish

-- R4 chain: (a, 0, c, 0, e+2*k) →* (a, 0, c+k, 0, e)
theorem r4_chain : ∀ k a c e, ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- R5+R1 chain: (a+k, 0, c+k, d, 0) →* (a, 0, c, d+2*k, 0)
theorem r5r1_chain : ∀ k a c d, ⟨a + k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2))
    ring_nf; finish

-- Opening: R5+R2: (1, 0, 0, d, 0) ⊢⁺ (0, 0, 0, d+1, 3)
theorem opening (d : ℕ) :
    ⟨1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 1, 3⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm; finish

-- Middle: R5+R1+R3+R1: (A+1, 0, C+2, 0, 1) ⊢* (A+1, 0, C, 2, 0)
theorem middle (A C : ℕ) :
    ⟨A + 1, 0, C + 2, 0, 1⟩ [fm]⊢* ⟨A + 1, 0, C, 2, 0⟩ := by
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm; ring_nf; finish

-- Main transition: (1, 0, 0, 2*n, 0) ⊢⁺ (1, 0, 0, 4*n+2, 0)
theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, 2 * n, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 4 * n + 2, 0⟩ := by
  -- Phase 0: opening
  apply stepPlus_stepStar_stepPlus (opening (2 * n))
  -- State: (0, 0, 0, 2n+1, 3)
  -- Phase 1: R3+R2 chain (2n+1 rounds)
  rw [show (2 * n + 1 : ℕ) = 0 + (2 * n + 1) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (2 * n + 1) 0 0 2)
  rw [show 0 + (2 * n + 1) = 2 * n + 1 from by ring,
      show 2 + 2 * (2 * n + 1) + 1 = 4 * n + 5 from by ring]
  -- Phase 2: R4 chain: (2n+1,0,0,0,4n+5) →* (2n+1,0,2n+2,0,1)
  rw [show (4 * n + 5 : ℕ) = 1 + 2 * (2 * n + 2) from by ring]
  apply stepStar_trans (r4_chain (2 * n + 2) (2 * n + 1) 0 1)
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring]
  -- Phase 3: middle steps
  rw [show (2 * n + 1 : ℕ) = (2 * n) + 1 from by ring,
      show (2 * n + 2 : ℕ) = (2 * n) + 2 from by ring]
  apply stepStar_trans (middle (2 * n) (2 * n))
  -- State: (2n+1, 0, 2n, 2, 0)
  -- Phase 4: R5+R1 chain (2n rounds)
  have phase4 := r5r1_chain (2 * n) 1 0 2
  rw [show 1 + 2 * n = 2 * n + 1 from by ring,
      show 0 + 2 * n = 2 * n from by ring,
      show 2 + 2 * (2 * n) = 4 * n + 2 from by ring] at phase4
  exact phase4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · execute fm 0
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 2 * n, 0⟩) 0
  intro n; refine ⟨2 * n + 1, ?_⟩
  rw [show 2 * (2 * n + 1) = 4 * n + 2 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1419
