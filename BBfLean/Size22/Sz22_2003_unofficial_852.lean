import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #852: [36/35, 5/3, 1/10, 2401/2, 3/7]

Vector representation:
```
 2  2 -1 -1
 0 -1  1  0
-1  0 -1  0
-1  0  0  4
 0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_852

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+2, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+4⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R2R1 chain: (a, b+1, 0, k) →* (a+2*k, b+1+k, 0, 0)
theorem r2r1_chain : ∀ k, ⟨a, b + 1, 0, k⟩ [fm]⊢* ⟨a + 2 * k, b + 1 + k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a := a + 2) (b := b + 1))
    ring_nf; finish

-- R2 chain: move b to c when d=0. (a, k, c, 0) →* (a, 0, c+k, 0)
theorem b_to_c : ∀ k, ⟨a, k, c, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R3 chain: (a+k, 0, k, 0) →* (a, 0, 0, 0) when b=0, d=0
theorem r3_chain : ∀ k, ⟨a + k, 0, k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    exact ih

-- R4 chain: (k, 0, 0, d) →* (0, 0, 0, d+4*k)
theorem r4_chain : ∀ k, ⟨k, 0, 0, d⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * k⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 4))
    ring_nf; finish

-- Main transition: (0, 0, 0, d+4) →⁺ (0, 0, 0, 4*d+8)
theorem main_trans (d : ℕ) : ⟨0, 0, 0, d + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * d + 8⟩ := by
  -- R5: (0,0,0,d+4) → (0,1,0,d+3)
  step fm
  -- R2: (0,1,0,d+3) → (0,0,1,d+3)
  rw [show d + 3 = d + 2 + 1 from by ring]
  step fm
  -- R1: (0,0,1,d+2+1) → (2,2,0,d+2)
  step fm
  -- R2R1 chain: (2, 2, 0, d+2) →* (2*d+6, d+4, 0, 0)
  apply stepStar_trans (r2r1_chain (d + 2) (a := 2) (b := 1))
  rw [show 2 + 2 * (d + 2) = 2 * d + 6 from by ring,
      show 1 + 1 + (d + 2) = d + 4 from by ring]
  -- R2 drain: (2*d+6, d+4, 0, 0) →* (2*d+6, 0, d+4, 0)
  apply stepStar_trans (b_to_c (d + 4) (a := 2 * d + 6) (c := 0))
  rw [show (0 : ℕ) + (d + 4) = d + 4 from by ring]
  -- R3 chain: (2*d+6, 0, d+4, 0) →* (d+2, 0, 0, 0)
  rw [show 2 * d + 6 = (d + 2) + (d + 4) from by ring]
  apply stepStar_trans (r3_chain (d + 4) (a := d + 2))
  -- R4 chain: (d+2, 0, 0, 0) →* (0, 0, 0, 4*(d+2))
  rw [show (0 : ℕ) = 0 + 4 * 0 from by ring]
  apply stepStar_trans (r4_chain (d + 2) (d := 0))
  rw [show 0 + 4 * (d + 2) = 4 * d + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4⟩) (by execute fm 1)
  rw [show (4 : ℕ) = 0 + 4 from by ring]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 4⟩) 0
  intro n; exact ⟨4 * n + 4, main_trans n⟩
