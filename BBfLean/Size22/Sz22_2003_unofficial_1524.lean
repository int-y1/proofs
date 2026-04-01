import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1524: [7/30, 12/77, 11/2, 25/11, 14/5]

Vector representation:
```
-1 -1 -1  1  0
 2  1  0 -1 -1
-1  0  0  0  1
 0  0  2  0 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1524

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3/R2 chain: each round R3 then R2 reduces d by 1, increases a and b by 1.
theorem r3r2_chain : ∀ k, ⟨a + 1, b, 0, k, 0⟩ [fm]⊢* ⟨a + k + 1, b + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show a + 1 = (a + 0) + 1 from by omega]
    step fm; step fm
    rw [show a + 0 + 2 = (a + 1) + 1 from by omega]
    apply stepStar_trans (ih (a := a + 1) (b := b + 1))
    ring_nf; finish

-- R3 drain: move a to e.
theorem r3_drain : ∀ k, ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (a := a) (b := b) (e := e + 1))
    ring_nf; finish

-- R4 drain: move e to c (doubling).
theorem r4_drain : ∀ k, ⟨0, b, c, 0, k⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

-- R5/R1 chain: each round R5 then R1.
theorem r5r1_chain : ∀ k, ⟨0, k, 2 * k + 2, d, 0⟩ [fm]⊢* ⟨0, 0, 2, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 from by omega,
        show (0 : ℕ) = 0 from rfl]
    step fm; step fm
    rw [show d + 1 + 1 = (d + 2) from by omega]
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

-- Main transition: (0, 0, 2, d+2, 0) →⁺ (0, 0, 2, 2*d+6, 0)
theorem main_trans : ⟨0, 0, 2, d + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 2, 2 * d + 6, 0⟩ := by
  step fm; step fm; step fm; step fm
  rw [show (1 : ℕ) = 0 + 1 from by omega]
  apply stepStar_trans (r3r2_chain (d + 3) (a := 0) (b := 0))
  rw [show 0 + (d + 3) + 1 = 0 + (d + 4) from by omega,
      show 0 + (d + 3) = d + 3 from by omega]
  apply stepStar_trans (r3_drain (d + 4) (a := 0) (b := d + 3) (e := 0))
  rw [show 0 + (d + 4) = d + 4 from by omega]
  apply stepStar_trans (r4_drain (d + 4) (b := d + 3) (c := 0))
  rw [show 0 + 2 * (d + 4) = 2 * (d + 3) + 2 from by ring]
  apply stepStar_trans (r5r1_chain (d + 3) (d := 0))
  rw [show 0 + 2 * (d + 3) = 2 * d + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 2, 0⟩) (by execute fm 14)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 2, d + 2, 0⟩) 0
  intro d; exists 2 * d + 4; exact main_trans
