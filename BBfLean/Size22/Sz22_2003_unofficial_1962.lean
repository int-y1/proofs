import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1962: [99/35, 1/6, 5/3, 2/55, 1617/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  0  0  0
 0 -1  1  0  0
 1  0 -1  0 -1
-1  1  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1962

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | _ => none

-- Phase 1a: R5/R2 drain. (2k+1, 0, 0, D, E) →* (1, 0, 0, D+2k, E+k)
theorem r5r2_drain : ∀ k D E, ⟨2 * k + 1, 0, 0, D, E⟩ [fm]⊢* ⟨1, 0, 0, D + 2 * k, E + k⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (D + 2) (E + 1))
    ring_nf; finish

-- Phase 1b: (1, 0, 0, D, E) →⁺ (0, 0, 1, D+2, E+1)
theorem last_r5_r3 : ⟨1, 0, 0, D, E⟩ [fm]⊢⁺ ⟨0, 0, 1, D + 2, E + 1⟩ := by
  step fm; step fm; finish

-- Phase 2: R1/R3 spiral. (0, B, 1, k+1, E) →* (0, B+k+2, 0, 0, E+k+1)
theorem r1r3_spiral : ∀ k B E, ⟨0, B, 1, k + 1, E⟩ [fm]⊢* ⟨0, B + k + 2, 0, 0, E + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro B E
  · step fm; finish
  · rw [show (k + 1) + 1 = k + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (B + 1) (E + 1))
    ring_nf; finish

-- Phase 3: R3 drain b to c. (0, k, C, 0, E) →* (0, 0, C+k, 0, E)
theorem r3_drain : ∀ k C E, ⟨0, k, C, 0, E⟩ [fm]⊢* ⟨0, 0, C + k, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro C E
  · exists 0
  · step fm
    apply stepStar_trans (ih (C + 1) E)
    ring_nf; finish

-- Phase 4: R4 chain. (A, 0, k, 0, E+k) →* (A+k, 0, 0, 0, E)
theorem r4_chain : ∀ k A E, ⟨A, 0, k, 0, E + k⟩ [fm]⊢* ⟨A + k, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · rw [show E + (k + 1) = E + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A + 1) E)
    ring_nf; finish

-- Main transition: (2a+3, 0, 0, 0, e) ⊢⁺ (2a+5, 0, 0, 0, e+a+1)
theorem main_trans (a e : ℕ) : ⟨2 * a + 3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2 * a + 5, 0, 0, 0, e + a + 1⟩ := by
  -- Phase 1a: drain to (1, 0, 0, 2a+2, e+a+1)
  apply stepStar_stepPlus_stepPlus (r5r2_drain (a + 1) 0 e)
  -- Phase 1b: (1, 0, 0, 2a+2, e+a+1) ⊢⁺ (0, 0, 1, 2a+4, e+a+2)
  rw [show 0 + 2 * (a + 1) = 2 * a + 2 from by ring,
      show e + (a + 1) = e + a + 1 from by ring]
  apply stepPlus_stepStar_stepPlus last_r5_r3
  -- Phase 2: R1/R3 spiral
  rw [show (2 * a + 2) + 2 = (2 * a + 3) + 1 from by ring,
      show (e + a + 1) + 1 = e + a + 2 from by ring]
  apply stepStar_trans (r1r3_spiral (2 * a + 3) 0 (e + a + 2))
  -- Phase 3: R3 drain
  rw [show 0 + (2 * a + 3) + 2 = 2 * a + 5 from by ring,
      show (e + a + 2) + (2 * a + 3) + 1 = e + 3 * a + 6 from by ring]
  apply stepStar_trans (r3_drain (2 * a + 5) 0 (e + 3 * a + 6))
  -- Phase 4: R4 chain
  rw [show 0 + (2 * a + 5) = 2 * a + 5 from by ring,
      show e + 3 * a + 6 = (e + a + 1) + (2 * a + 5) from by ring]
  apply stepStar_trans (r4_chain (2 * a + 5) 0 (e + a + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 0⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨2 * a + 3, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨a, e⟩; exact ⟨⟨a + 1, e + a + 1⟩, main_trans a e⟩
