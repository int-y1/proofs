import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1472: [7/15, 36/77, 121/3, 5/2, 21/5]

Vector representation:
```
 0 -1 -1  1  0
 2  2  0 -1 -1
 0 -1  0  0  2
-1  0  1  0  0
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1472

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R2+R1+R1 chain: each round does R2, R1, R1 consuming 2 from c and 1 from e.
-- (a, 0, 2*k, d+2, e+k) →* (a+2*k, 0, 0, d+k+2, e)
theorem r2r1r1_chain : ∀ k a d e, ⟨a, 0, 2 * k, d + 2, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k + 2, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) (d + 1) e)
    ring_nf; finish

-- R2 chain: drain d using e.
-- (a, b, 0, k, e+k) →* (a+2*k, b+2*k, 0, 0, e)
theorem r2_chain : ∀ k a b e, ⟨a, b, 0, k, e + k⟩ [fm]⊢* ⟨a + 2 * k, b + 2 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) (b + 2) e)
    ring_nf; finish

-- R3 chain: drain b to e.
-- (a, k, 0, 0, e) →* (a, 0, 0, 0, e+2*k)
theorem r3_chain : ∀ k a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih a (e + 2))
    ring_nf; finish

-- R4 chain: drain a to c.
-- (k, 0, c, 0, e) →* (0, 0, c+k, 0, e)
theorem r4_chain : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- Main transition:
-- (0, 0, 2*(c+1), 0, 2*(c+1)+f+3) ⊢⁺ (0, 0, 4*(c+1), 0, 4*(c+1)+f+7)
-- i.e., (0, 0, 2c+2, 0, 2c+f+5) ⊢⁺ (0, 0, 4c+4, 0, 4c+f+11)
theorem main_trans (c f : ℕ) :
    ⟨0, 0, 2 * c + 2, 0, 2 * c + f + 5⟩ [fm]⊢⁺ ⟨0, 0, 4 * c + 4, 0, 4 * c + f + 11⟩ := by
  -- Phase 1: R5 + R1 (2 steps)
  rw [show 2 * c + 2 = (2 * c + 1) + 1 from by ring]
  step fm -- R5: (0, 1, 2c+1, 1, 2c+f+5)
  rw [show (2 * c + 1 : ℕ) = (2 * c) + 1 from by ring]
  step fm -- R1: (0, 0, 2c, 2, 2c+f+5)
  -- Phase 2: R2+R1+R1 chain (c rounds)
  -- (0, 0, 2*c, 0+2, (c+f+5)+c) →* (0+2*c, 0, 0, 0+c+2, c+f+5)
  rw [show (2 * c + f + 5 : ℕ) = (c + f + 5) + c from by ring]
  apply stepStar_trans (r2r1r1_chain c 0 0 (c + f + 5))
  -- State: (2*c, 0, 0, c+2, c+f+5)
  -- Phase 3: R2 chain (c+2 rounds), drain d using e
  -- (2*c, 0, 0, c+2, c+f+5) = (2*c, 0, 0, c+2, (f+3)+(c+2))
  rw [show (0 + 2 * c : ℕ) = 2 * c from by ring,
      show (0 + c + 2 : ℕ) = c + 2 from by ring,
      show c + f + 5 = (f + 3) + (c + 2) from by ring]
  apply stepStar_trans (r2_chain (c + 2) (2 * c) 0 (f + 3))
  -- State: (2*c+2*(c+2), 2*(c+2), 0, 0, f+3) = (4*c+4, 2*c+4, 0, 0, f+3)
  rw [show 2 * c + 2 * (c + 2) = 4 * c + 4 from by ring,
      show (0 + 2 * (c + 2) : ℕ) = 2 * c + 4 from by ring]
  -- Phase 4: R3 chain (2*c+4 rounds), drain b to e
  apply stepStar_trans (r3_chain (2 * c + 4) (4 * c + 4) (f + 3))
  -- State: (4*c+4, 0, 0, 0, f+3+2*(2*c+4)) = (4*c+4, 0, 0, 0, 4*c+f+11)
  rw [show f + 3 + 2 * (2 * c + 4) = 4 * c + f + 11 from by ring]
  -- Phase 5: R4 chain (4*c+4 rounds), drain a to c
  apply stepStar_trans (r4_chain (4 * c + 4) 0 (4 * c + f + 11))
  -- State: (0, 0, 4*c+4, 0, 4*c+f+11)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 5⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, f⟩ ↦ ⟨0, 0, 2 * (c + 1), 0, 2 * (c + 1) + f + 3⟩) ⟨0, 0⟩
  intro ⟨c, f⟩; refine ⟨⟨2 * c + 1, f + 4⟩, ?_⟩
  show ⟨0, 0, 2 * (c + 1), 0, 2 * (c + 1) + f + 3⟩ [fm]⊢⁺
       ⟨0, 0, 2 * (2 * c + 1 + 1), 0, 2 * (2 * c + 1 + 1) + (f + 4) + 3⟩
  convert main_trans c f using 2; ring_nf

end Sz22_2003_unofficial_1472
