import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1544: [7/30, 363/2, 4/21, 5/3, 6/11]

Vector representation:
```
-1 -1 -1  1  0
-1  1  0  0  2
 2 -1  0 -1  0
 0 -1  1  0  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1544

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R3,R2,R2 chain: each round drains 1 from d, adds 1 to b, adds 4 to e.
theorem r3r2r2_chain : ∀ k, ∀ b e, ⟨0, b + 1, 0, k, e⟩ [fm]⊢* ⟨0, b + k + 1, 0, 0, e + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 1) (e + 4)); ring_nf; finish

-- R4 chain: transfer b to c.
theorem r4_chain : ∀ k, ∀ c e, ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R5,R1 chain: each round drains 1 from c and 1 from e, adds 1 to d.
theorem r5r1_chain : ∀ k, ∀ d e, ⟨0, 0, k, d, e + k⟩ [fm]⊢* ⟨0, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d + 1) e); ring_nf; finish

-- Main transition: (0,0,0,d+1,e+1) ⊢⁺ (0,0,0,d+3,e+3*d+3)
-- Phase 1: R5: (0,0,0,d+1,e+1) -> (1,1,0,d+1,e)
-- Phase 2: R2: (1,1,0,d+1,e) -> (0,2,0,d+1,e+2)
-- Phase 3: R3,R2,R2 chain (d+1 rounds): (0,2,0,d+1,e+2) -> (0,d+3,0,0,e+4d+6)
-- Phase 4: R4 chain (d+3 rounds): (0,d+3,0,0,e+4d+6) -> (0,0,d+3,0,e+4d+6)
-- Phase 5: R5,R1 chain (d+3 rounds): (0,0,d+3,0,e+4d+6) -> (0,0,0,d+3,e+3d+3)
--   since e+4d+6 = (e+3d+3) + (d+3)
theorem main_trans (d e : ℕ) :
    ⟨0, 0, 0, d + 1, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 3, e + 3 * d + 3⟩ := by
  -- Phase 1: R5
  step fm
  -- Phase 2: R2
  step fm
  -- Phase 3: R3,R2,R2 chain
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show e + 2 = e + 2 + 4 * 0 from by ring]
  apply stepStar_trans (r3r2r2_chain (d + 1) 1 (e + 2))
  -- After: (0, 1+(d+1)+1, 0, 0, e+2+4*(d+1)) = (0, d+3, 0, 0, e+4*d+6)
  -- Phase 4: R4 chain
  rw [show 1 + (d + 1) + 1 = d + 3 from by ring,
      show e + 2 + 4 * (d + 1) = e + 4 * d + 6 from by ring]
  apply stepStar_trans (r4_chain (d + 3) 0 (e + 4 * d + 6))
  -- After: (0, 0, d+3, 0, e+4*d+6)
  -- Phase 5: R5,R1 chain
  rw [show 0 + (d + 3) = d + 3 from by ring,
      show e + 4 * d + 6 = (e + 3 * d + 3) + (d + 3) from by ring]
  apply stepStar_trans (r5r1_chain (d + 3) 0 (e + 3 * d + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 1, e + 1⟩) ⟨0, 0⟩
  intro ⟨d, e⟩; exact ⟨⟨d + 2, e + 3 * d + 2⟩, main_trans d e⟩

end Sz22_2003_unofficial_1544
