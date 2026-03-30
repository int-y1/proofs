import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #837: [36/35, 15/2, 1/45, 49/3, 5/7]

Vector representation:
```
 2  2 -1 -1
-1  1  1  0
 0 -2 -1  0
 0 -1  0  2
 0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_837

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+2, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c+1, d⟩
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | _ => none

-- Spiral: R1+R2 alternating.
-- (a, b, 1, k) →* (a+k, b+3*k, 1, 0)
theorem spiral : ∀ k, ⟨a, b, 1, k⟩ [fm]⊢* ⟨a + k, b + 3 * k, 1, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show (1 : ℕ) = 0 + 1 from by ring, show k + 1 = k + (0 + 1) from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a + 1) (b := b + 3))
    ring_nf; finish

-- R2 drain: (a, b, c, 0) →* (0, b+a, c+a, 0)
theorem r2_drain : ∀ a, ⟨a, b, c, 0⟩ [fm]⊢* ⟨0, b + a, c + a, 0⟩ := by
  intro a; induction' a with a ih generalizing b c
  · exists 0
  · step fm
    apply stepStar_trans (ih (b := b + 1) (c := c + 1))
    ring_nf; finish

-- R3 drain: (0, b, k, 0) →* (0, b-2*k, 0, 0)
-- Rewritten: (0, b+2*k, k, 0) →* (0, b, 0, 0)
theorem r3_drain : ∀ k b, ⟨0, b + 2 * k, k, 0⟩ [fm]⊢* ⟨0, b, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    exact ih b

-- R4 drain: (0, b, 0, d) →* (0, 0, 0, d+2*b)
theorem r4_drain : ∀ b, ⟨0, b, 0, d⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * b⟩ := by
  intro b; induction' b with b ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

-- Main transition: (0, 0, 0, k+4) →⁺ (0, 0, 0, 4*k+8)
theorem main_trans : ⟨0, 0, 0, k + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * k + 8⟩ := by
  rw [show k + 4 = k + 3 + 1 from by ring]
  step fm
  apply stepStar_trans (spiral (k + 3) (a := 0) (b := 0))
  rw [show 0 + (k + 3) = k + 3 from by ring,
      show 0 + 3 * (k + 3) = 3 * k + 9 from by ring]
  apply stepStar_trans (r2_drain (k + 3) (b := 3 * k + 9) (c := 1))
  rw [show 3 * k + 9 + (k + 3) = 4 * k + 12 from by ring,
      show 1 + (k + 3) = k + 4 from by ring]
  rw [show 4 * k + 12 = (2 * k + 4) + 2 * (k + 4) from by ring]
  apply stepStar_trans (r3_drain (k + 4) (2 * k + 4))
  apply stepStar_trans (r4_drain (2 * k + 4) (d := 0))
  rw [show 0 + 2 * (2 * k + 4) = 4 * k + 8 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4⟩) (by execute fm 13)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 4⟩) 0
  intro n; exists 4 * n + 4; exact main_trans

end Sz22_2003_unofficial_837
