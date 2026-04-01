import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1541: [7/30, 33/2, 12/77, 5/11, 14/3]

Vector representation:
```
-1 -1 -1  1  0
-1  1  0  0  1
 2  1  0 -1 -1
 0  0  1  0 -1
 1 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1541

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3R2R2 chain: each round (0, B, 0, D+1, E+1) -> (0, B+3, 0, D, E+2)
-- After k rounds: (0, B, 0, D+k, E+1) -> (0, B+3*k, 0, D, E+1+k)
theorem r3r2r2_chain : ∀ k, ∀ B D E, ⟨0, B, 0, D + k, E + 1⟩ [fm]⊢*
    ⟨0, B + 3 * k, 0, D, E + 1 + k⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (B + 3) D (E + 1)); ring_nf; finish

-- R4 chain: transfer e to c (with a=0, b unchanged, d=0)
theorem e_to_c : ∀ k, ∀ B C, ⟨0, B, C, 0, k⟩ [fm]⊢* ⟨0, B, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro B C
  · exists 0
  · rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih B (C + 1)); ring_nf; finish

-- R5R1 chain: (0, B+2*k, C+k, D, 0) -> (0, B, C, D+2*k, 0)
theorem r5r1_chain : ∀ k, ∀ B C D, ⟨0, B + 2 * k, C + k, D, 0⟩ [fm]⊢*
    ⟨0, B, C, D + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro B C D
  · exists 0
  · rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
        show C + (k + 1) = (C + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih B C (D + 2)); ring_nf; finish

-- Main transition: (0, b+1, 0, d+4, 0) ⊢⁺ (0, b+d+4, 0, 2*d+12, 0)
theorem main_trans (b d : ℕ) :
    ⟨0, b + 1, 0, d + 4, 0⟩ [fm]⊢⁺ ⟨0, b + d + 4, 0, 2 * d + 12, 0⟩ := by
  -- Phase 1: Opening R5, R2
  step fm; step fm
  -- State: (0, b+1, 0, d+5, 1)
  -- Phase 2: R3R2R2 chain with d+5 rounds
  rw [show d + 5 = 0 + (d + 5) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (d + 5) (b + 1) 0 0)
  -- State: (0, b+1+3*(d+5), 0, 0, 0+1+(d+5))
  rw [show b + 1 + 3 * (d + 5) = b + 3 * d + 16 from by ring,
      show 0 + 1 + (d + 5) = d + 6 from by ring]
  -- Phase 3: R4 chain: e -> c
  apply stepStar_trans (e_to_c (d + 6) (b + 3 * d + 16) 0)
  -- State: (0, b+3*d+16, 0+(d+6), 0, 0)
  -- Phase 4: R5R1 chain with d+6 rounds
  show ⟨0, b + 3 * d + 16, 0 + (d + 6), 0, 0⟩ [fm]⊢* ⟨0, b + d + 4, 0, 2 * d + 12, 0⟩
  rw [show b + 3 * d + 16 = (b + d + 4) + 2 * (d + 6) from by ring]
  apply stepStar_trans (r5r1_chain (d + 6) (b + d + 4) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 4, 0⟩)
  · execute fm 16
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨b, d⟩ ↦ ⟨0, b + 1, 0, d + 4, 0⟩) ⟨0, 0⟩
  intro ⟨b, d⟩; exact ⟨⟨b + d + 3, 2 * d + 8⟩, main_trans b d⟩

end Sz22_2003_unofficial_1541
