import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1531: [7/30, 22/3, 18/77, 5/11, 9/2]

Vector representation:
```
-1 -1 -1  1  0
 1 -1  0  0  1
 1  2  0 -1 -1
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1531

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R3+R2+R2 chain: each round drains d by 1 and grows a by 3, e by 1
-- (a, 0, 0, d+k, e) with e >= 1 -> (a+3*k, 0, 0, d, e+k)
theorem r3r2r2_chain : ∀ k, ∀ a d e, ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (a + 3) d (e + 1)); ring_nf; finish

-- R4 chain: convert e to c
theorem e_to_c : ∀ k, ∀ a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih a (c + 1)); ring_nf; finish

-- R5+R1+R1 chain: drains c by 2 and a by 3 per round, grows d by 2
theorem r5r1r1_chain : ∀ k, ∀ a d, ⟨a + 3 * k, 0, 2 * k, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
      show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih a (d + 2)); ring_nf; finish

-- Main transition: (a+1, 0, 0, 2*n+2, 0) ⊢⁺ (a+3*n+2, 0, 0, 2*n+4, 0)
theorem main_trans (a n : ℕ) :
    ⟨a + 1, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨a + 3 * n + 2, 0, 0, 2 * n + 4, 0⟩ := by
  -- Phase 1: R5+R2+R2 opening: (a+1, 0, 0, 2n+2, 0) -> (a+2, 0, 0, 2n+2, 2)
  step fm; step fm; step fm
  -- Phase 2: R3+R2+R2 chain for (2n+2) rounds
  -- Start: (a+2, 0, 0, 2n+2, 2) = (a+2, 0, 0, 0+(2n+2), 1+1)
  -- Result: (a+2+3*(2n+2), 0, 0, 0, 1+(2n+2)+1) = (a+6n+8, 0, 0, 0, 2n+4)
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r3r2r2_chain (2 * n + 2) (a + 2) 0 1)
  -- Now: (a+2+3*(2n+2), 0, 0, 0, 1+(2n+2)+1) = (a+6n+8, 0, 0, 0, 2n+4)
  -- Phase 3: R4 chain to convert e to c
  rw [show a + 2 + 3 * (2 * n + 2) = a + 6 * n + 8 from by ring,
      show 1 + (2 * n + 2) + 1 = 2 * n + 4 from by ring]
  apply stepStar_trans (e_to_c (2 * n + 4) (a + 6 * n + 8) 0)
  -- Now: (a+6n+8, 0, 2n+4, 0, 0)
  -- Phase 4: R5+R1+R1 chain for (n+2) rounds
  -- Need: a+6n+8 = (a+3n+2) + 3*(n+2) and 2n+4 = 2*(n+2)
  rw [show (0 + (2 * n + 4) : ℕ) = 2 * (n + 2) from by ring,
      show a + 6 * n + 8 = (a + 3 * n + 2) + 3 * (n + 2) from by ring]
  apply stepStar_trans (r5r1r1_chain (n + 2) (a + 3 * n + 2) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 19)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a + 1, 0, 0, 2 * n + 2, 0⟩) ⟨1, 0⟩
  intro ⟨a, n⟩; exact ⟨⟨a + 3 * n + 1, n + 1⟩, main_trans a n⟩

end Sz22_2003_unofficial_1531
