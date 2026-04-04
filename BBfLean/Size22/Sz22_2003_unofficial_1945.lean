import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1945: [9/70, 5/33, 847/5, 4/11, 5/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1  1  0 -1
 0  0 -1  1  2
 2  0  0  0 -1
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1945

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: drain e into a (2 per step)
theorem e_to_a : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

-- R5+R1 chain: drain d to b, two steps per round
theorem r5_r1_chain : ∀ k, ∀ a b, ⟨a + 2 * k, b, 0, k, 0⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a) (b := b + 2))
    ring_nf; finish

-- R3+R2+R2 chain: drain b (by 2 per round), grow c and d
theorem r3_r2_r2_chain : ∀ k, ∀ c d, ⟨0, 2 * k, c + 1, d, 0⟩ [fm]⊢* ⟨0, 0, c + 1 + k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (c := c + 1) (d := d + 1))
    ring_nf; finish

-- R3 chain: drain c, grow d and e
theorem r3_chain : ∀ k, ∀ d e, ⟨0, 0, k, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 2))
    ring_nf; finish

-- Middle transition: (2, 2*(d+1), 0, 0, 0) → (0, 2*(d+1), 1, 0, 0) in 5 steps
theorem middle : ⟨2, b + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨0, b + 1, 1, 0, 0⟩ := by
  step fm
  step fm
  step fm
  step fm
  step fm
  finish

-- Main transition: (0, 0, 0, d+1, d+2) ⊢⁺ (0, 0, 0, 2*d+3, 2*d+4)
theorem main_trans : ⟨0, 0, 0, d + 1, d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 3, 2 * d + 4⟩ := by
  -- Phase 1: R4 chain, drain e = d+2
  rw [show (d + 2 : ℕ) = 0 + (d + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_a (d + 2) (a := 0) (d := d + 1) (e := 0))
  -- Now at (2*(d+2), 0, 0, d+1, 0) = (2*d+4, 0, 0, d+1, 0)
  -- Phase 2: R5+R1 chain, d+1 rounds
  rw [show 0 + 2 * (d + 2) = 2 + 2 * (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5_r1_chain (d + 1) (a := 2) (b := 0))
  -- Phase 3: R5 + middle (5 steps)
  rw [show 0 + 2 * (d + 1) = (2 * d + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (middle (b := 2 * d + 1))
  -- Phase 5: R3+R2+R2 chain, d+1 rounds
  rw [show (2 * d + 1) + 1 = 2 * (d + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3_r2_r2_chain (d + 1) (c := 0) (d := 0))
  -- Phase 6: R3 chain, d+2 steps
  rw [show 0 + 1 + (d + 1) = d + 2 from by ring,
      show 0 + (d + 1) = d + 1 from by ring]
  apply stepStar_trans (r3_chain (d + 2) (d := d + 1) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d + 1, d + 2⟩) 0
  intro d; exists 2 * d + 2
  exact main_trans
