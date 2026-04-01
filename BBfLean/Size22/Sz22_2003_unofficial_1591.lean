import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1591: [72/35, 5/3, 1/10, 49/2, 10/7]

Vector representation:
```
 3  2 -1 -1
 0 -1  1  0
-1  0 -1  0
-1  0  0  2
 1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1591

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+3, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b, c+1, d⟩
  | _ => none

-- R2+R1 interleaved chain: (a, b+1, 0, d+k) →* (a+3k, b+k+1, 0, d)
theorem r2r1_chain : ∀ k, ⟨a, b + 1, 0, d + k⟩ [fm]⊢* ⟨a + 3 * k, b + k + 1, 0, d⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a + 3) (b := b + 1) (d := d))
    ring_nf; finish

-- R2 chain: (a, b+k, c, 0) →* (a, b, c+k, 0)
theorem b_to_c : ∀ k, ⟨a, b + k, c, 0⟩ [fm]⊢* ⟨a, b, c + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R3 chain: (a+k, 0, c+k, 0) →* (a, 0, c, 0)
theorem r3_chain : ∀ k, ⟨a + k, 0, c + k, 0⟩ [fm]⊢* ⟨a, 0, c, 0⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; exact ih

-- R4 chain: (a+k, 0, 0, d) →* (a, 0, 0, d+2k)
theorem a_to_d : ∀ k, ⟨a + k, 0, 0, d⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

-- Full cycle: (0, 0, 0, D+2) →⁺ (0, 0, 0, 4D+4)
theorem main_trans (D : ℕ) : ⟨0, 0, 0, D + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * D + 4⟩ := by
  step fm; step fm
  -- After R5+R1: (4, 2, 0, D)
  rw [show (2 : ℕ) = 1 + 1 from by omega,
      show (D : ℕ) = 0 + D from by omega]
  apply stepStar_trans (r2r1_chain D (a := 4) (b := 1) (d := 0))
  rw [show 1 + D + 1 = 0 + (D + 2) from by ring]
  apply stepStar_trans (b_to_c (D + 2) (a := 4 + 3 * D) (b := 0) (c := 0))
  rw [show 4 + 3 * D = (2 * D + 2) + (D + 2) from by ring,
      show 0 + (D + 2) = 0 + (D + 2) from rfl]
  apply stepStar_trans (r3_chain (D + 2) (a := 2 * D + 2) (c := 0))
  rw [show 2 * D + 2 = 0 + (2 * D + 2) from by ring]
  apply stepStar_trans (a_to_d (2 * D + 2) (a := 0) (d := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun D ↦ ⟨0, 0, 0, D + 2⟩) 0
  intro D; exists 4 * D + 2
  exact main_trans D

end Sz22_2003_unofficial_1591
