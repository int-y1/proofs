import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1351: [63/10, 363/2, 4/77, 5/3, 7/11]

Vector representation:
```
-1  2 -1  1  0
-1  1  0  0  2
 2  0  0 -1 -1
 0 -1  1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1351

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: convert b to c (a=0, d=0)
theorem b_to_c : ∀ k b c e, ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) e)
    ring_nf; finish

-- R3R2R2 chain: drain d (a=0, c=0)
-- One round: (0, b, 0, k+1, e+1) -> R3(2,b,0,k,e) -> R2(1,b+1,0,k,e+2) -> R2(0,b+2,0,k,e+4)
theorem r3r2r2_chain : ∀ k b e, ⟨0, b, 0, k, e + 1⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 0, e + 1 + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm
    rw [show b + 1 + 1 = (b + 2) from by ring,
        show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (b + 2) (e + 3))
    ring_nf; finish

-- Spiral core: k rounds of (R3, R1, R1)
-- (0, B, 2k+1+2, (D+1)+1, (E+k)+1) -> R3(2, B, 2k+3, D+1, E+k)
--   -> R1(1, B+2, 2k+2, D+2, E+k) -> R1(0, B+4, 2k+1, D+3, E+k)
theorem spiral_core : ∀ k B D E,
    ⟨0, B, 2 * k + 1, D + 2, E + k⟩ [fm]⊢* ⟨0, B + 4 * k, 1, D + k + 2, E⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show D + 2 = (D + 1) + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show B + 2 + 2 = (B + 4) from by ring,
        show D + 1 + 1 + 1 = (D + 1) + 2 from by ring,
        show E + k = E + k from rfl]
    apply stepStar_trans (ih (B + 4) (D + 1) E)
    ring_nf; finish

-- Spiral for k=0: (0,0,1,0,E+2) -> R5,R3,R1,R2 -> (0,3,0,1,E+2)
theorem spiral_base (E : ℕ) : ⟨0, 0, 1, 0, E + 2⟩ [fm]⊢* ⟨0, 3, 0, 1, E + 2⟩ := by
  rw [show E + 2 = (E + 1) + 1 from by ring]
  step fm  -- R5: (0,0,1,1,E+1)
  rw [show E + 1 = E + 1 from rfl]
  step fm  -- R3: (2,0,1,0,E)
  step fm  -- R1: (1,2,0,1,E)
  step fm  -- R2: (0,3,0,1,E+2)
  finish

-- Spiral for k>=1: (0,0,2k+3,0,E+k+3) -> ... -> (0,4k+7,0,k+2,E+2)
theorem spiral_step (k E : ℕ) :
    ⟨0, 0, 2 * k + 3, 0, E + k + 3⟩ [fm]⊢* ⟨0, 4 * k + 7, 0, k + 2, E + 2⟩ := by
  rw [show E + k + 3 = (E + k + 2) + 1 from by ring]
  step fm  -- R5: (0,0,2k+3,1,E+k+2)
  rw [show E + k + 2 = (E + k + 1) + 1 from by ring]
  step fm  -- R3: (2,0,2k+3,0,E+k+1)
  step fm  -- R1: (1,2,2k+2,1,E+k+1)
  step fm  -- R1: (0,4,2k+1,2,E+k+1)
  rw [show (4 : ℕ) = 4 from rfl,
      show (2 : ℕ) = 0 + 2 from by ring,
      show E + k + 1 = (E + 1) + k from by ring]
  apply stepStar_trans (spiral_core k 4 0 (E + 1))
  rw [show 4 + 4 * k = 4 * k + 4 from by ring,
      show 0 + k + 2 = (k + 1) + 1 from by ring,
      show E + 1 = E + 1 from rfl]
  step fm  -- R3: (2, 4k+4, 1, k+1, E)
  step fm  -- R1: (1, 4k+6, 0, k+2, E)
  step fm  -- R2: (0, 4k+7, 0, k+2, E+2)
  ring_nf; finish

-- Full spiral
theorem spiral (k E : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, E + k + 2⟩ [fm]⊢* ⟨0, 4 * k + 3, 0, k + 1, E + 2⟩ := by
  rcases k with _ | k
  · exact spiral_base E
  · rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring,
        show E + (k + 1) + 2 = E + k + 3 from by ring,
        show 4 * (k + 1) + 3 = 4 * k + 7 from by ring,
        show (k : ℕ) + 1 + 1 = k + 2 from by ring]
    exact spiral_step k E

-- Main transition: (0,0,2k+1,0,E+k+2) ⊢⁺ (0,0,6k+5,0,E+3k+5)
theorem main_trans (k E : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, E + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 6 * k + 5, 0, E + 3 * k + 5⟩ := by
  -- Phase 1: Spiral to (0, 4k+3, 0, k+1, E+2)
  apply stepStar_stepPlus_stepPlus (spiral k E)
  -- Phase 2: R3R2R2 chain draining d = k+1
  rw [show E + 2 = (E + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r3r2r2_chain (k + 1) (4 * k + 3) (E + 1))
  rw [show 4 * k + 3 + 2 * (k + 1) = 6 * k + 5 from by ring,
      show E + 1 + 1 + 3 * (k + 1) = E + 3 * k + 5 from by ring]
  -- Phase 3: R4 chain converting b = 6k+5 to c
  -- Take one R4 step, then use b_to_c for the rest
  rw [show (6 * k + 5 : ℕ) = (6 * k + 4) + 1 from by ring]
  step fm  -- R4: (0, 6k+4, 1, 0, E+3k+5)
  rw [show (6 * k + 4 : ℕ) = 0 + (6 * k + 4) from by ring]
  apply stepStar_trans (b_to_c (6 * k + 4) 0 1 (E + 3 * k + 5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, E⟩ ↦ ⟨0, 0, 2 * k + 1, 0, E + k + 2⟩) ⟨0, 0⟩
  intro ⟨k, E⟩
  exact ⟨⟨3 * k + 2, E + 1⟩, by
    show ⟨0, 0, 2 * k + 1, 0, E + k + 2⟩ [fm]⊢⁺
      ⟨0, 0, 2 * (3 * k + 2) + 1, 0, (E + 1) + (3 * k + 2) + 2⟩
    rw [show 2 * (3 * k + 2) + 1 = 6 * k + 5 from by ring,
        show (E + 1) + (3 * k + 2) + 2 = E + 3 * k + 5 from by ring]
    exact main_trans k E⟩
