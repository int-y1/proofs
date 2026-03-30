import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #657: [35/6, 1573/2, 4/55, 3/7, 35/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  2  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_657

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | _ => none

-- R4 repeated: move d to b.
theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

-- Phase A+B: d_to_b followed by R5.
-- (0, 0, 0, d, e, f+1) ⊢⁺ (0, d, 1, 1, e, f)
theorem d_to_b_r5 : ∀ d, (⟨0, 0, 0, d, e, f + 1⟩ : Q) [fm]⊢⁺ ⟨0, d, 1, 1, e, f⟩ := by
  intro d
  apply stepStar_step_stepPlus
  · rw [show (d : ℕ) = 0 + d from by ring]
    exact d_to_b d (b := 0) (d := 0) (e := e) (f := f + 1)
  · simp [fm]

-- One interleave round: R3, R1, R1.
-- (0, b+2, c+1, D, E+1, F) ⊢* (0, b, c+2, D+2, E, F)
theorem interleave_one : ⟨0, b + 2, c + 1, D, E + 1, F⟩ [fm]⊢*
    ⟨0, b, c + 2, D + 2, E, F⟩ := by
  execute fm 3

-- Interleave chain: k rounds.
theorem interleave_chain : ∀ k, ∀ b c D E F,
    ⟨0, 2 * k + b, c + 1, D, E + k, F⟩ [fm]⊢*
    ⟨0, b, c + k + 1, D + 2 * k, E, F⟩ := by
  intro k; induction' k with k ih <;> intro b c D E F
  · simp; exists 0
  · rw [show 2 * (k + 1) + b = (2 * k + b) + 2 from by ring,
        show E + (k + 1) = E + k + 1 from by ring]
    apply stepStar_trans (interleave_one (b := 2 * k + b) (c := c) (D := D) (E := E + k) (F := F))
    rw [show c + 2 = (c + 1) + 1 from by ring,
        show D + 2 = D + 2 from rfl,
        show c + (k + 1) + 1 = (c + 1) + k + 1 from by ring,
        show D + 2 * (k + 1) = (D + 2) + 2 * k from by ring]
    exact ih b (c + 1) (D + 2) E F

-- Odd remainder: R3, R1, R2.
theorem odd_remainder : ⟨0, 1, c + 1, D, E + 1, F⟩ [fm]⊢*
    ⟨0, 0, c + 1, D + 1, E + 2, F + 1⟩ := by
  execute fm 3

-- Tail chain: k rounds of (R3, R2, R2).
-- One round: (0, 0, c+1, D, E+1, F) ⊢* (0, 0, c, D, E+4, F+2)
theorem tail_one : ⟨0, 0, c + 1, D, E + 1, F⟩ [fm]⊢*
    ⟨0, 0, c, D, E + 4, F + 2⟩ := by
  execute fm 3

theorem tail_chain : ∀ k, ∀ c D E F,
    ⟨0, 0, c + k, D, E + k, F⟩ [fm]⊢*
    ⟨0, 0, c, D, E + 4 * k, F + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c D E F
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    apply stepStar_trans (tail_one (c := c + k) (D := D) (E := E + k) (F := F))
    rw [show E + k + 4 = (E + 4) + k from by ring,
        show E + 4 * (k + 1) = (E + 4) + 4 * k from by ring,
        show F + 2 * (k + 1) = (F + 2) + 2 * k from by ring]
    exact ih c D (E + 4) (F + 2)

-- Full transition for even d = 2*k.
theorem even_trans (k g : ℕ) : (⟨0, 0, 0, 2 * k, g + 4 * k + 2, g + 1⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 1, g + 6 * k + 5, g + 2 * k + 2⟩ := by
  apply stepPlus_stepStar_stepPlus (d_to_b_r5 (2 * k) (e := g + 4 * k + 2) (f := g))
  rw [show g + 4 * k + 2 = (g + 3 * k + 2) + k from by ring,
      show (2 * k : ℕ) = 2 * k + 0 from by ring]
  apply stepStar_trans (interleave_chain k 0 0 1 (g + 3 * k + 2) g)
  rw [show 0 + k + 1 = 0 + (k + 1) from by ring,
      show 1 + 2 * k = 2 * k + 1 from by ring,
      show g + 3 * k + 2 = (g + 2 * k + 1) + (k + 1) from by ring]
  apply stepStar_trans (tail_chain (k + 1) 0 (2 * k + 1) (g + 2 * k + 1) g)
  rw [show g + 2 * k + 1 + 4 * (k + 1) = g + 6 * k + 5 from by ring,
      show g + 2 * (k + 1) = g + 2 * k + 2 from by ring]
  finish

-- Full transition for odd d = 2*k+1.
theorem odd_trans (k g : ℕ) : (⟨0, 0, 0, 2 * k + 1, g + 4 * k + 4, g + 1⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 2, g + 6 * k + 8, g + 2 * k + 3⟩ := by
  apply stepPlus_stepStar_stepPlus (d_to_b_r5 (2 * k + 1) (e := g + 4 * k + 4) (f := g))
  rw [show g + 4 * k + 4 = (g + 3 * k + 4) + k from by ring,
      show (2 * k + 1 : ℕ) = 2 * k + 1 from rfl]
  apply stepStar_trans (interleave_chain k 1 0 1 (g + 3 * k + 4) g)
  rw [show 0 + k + 1 = k + 1 from by ring,
      show 1 + 2 * k = 2 * k + 1 from by ring,
      show g + 3 * k + 4 = (g + 3 * k + 3) + 1 from by ring]
  apply stepStar_trans (odd_remainder (c := k) (D := 2 * k + 1) (E := g + 3 * k + 3) (F := g))
  rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
      show g + 3 * k + 3 + 2 = g + 3 * k + 5 from by ring,
      show k + 1 = 0 + (k + 1) from by ring,
      show g + 3 * k + 5 = (g + 2 * k + 4) + (k + 1) from by ring]
  apply stepStar_trans (tail_chain (k + 1) 0 (2 * k + 2) (g + 2 * k + 4) (g + 1))
  rw [show g + 2 * k + 4 + 4 * (k + 1) = g + 6 * k + 8 from by ring,
      show g + 1 + 2 * (k + 1) = g + 2 * k + 3 from by ring]
  finish

-- Main transition using parity split.
theorem main_trans (d g : ℕ) : (⟨0, 0, 0, d, g + 2 * d + 2, g + 1⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 0, d + 1, (g + d + 1) + 2 * (d + 1) + 2, (g + d + 1) + 1⟩ := by
  rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    rw [show g + 2 * (2 * k) + 2 = g + 4 * k + 2 from by ring,
        show (g + 2 * k + 1) + 2 * (2 * k + 1) + 2 = g + 6 * k + 5 from by ring,
        show (g + 2 * k + 1) + 1 = g + 2 * k + 2 from by ring]
    exact even_trans k g
  · subst hk
    rw [show g + 2 * (2 * k + 1) + 2 = g + 4 * k + 4 from by ring,
        show (g + (2 * k + 1) + 1) + 2 * (2 * k + 1 + 1) + 2 = g + 6 * k + 8 from by ring,
        show (g + (2 * k + 1) + 1) + 1 = g + 2 * k + 3 from by ring,
        show 2 * k + 1 + 1 = 2 * k + 2 from by ring]
    exact odd_trans k g

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 0 + 2 * 0 + 2, 0 + 1⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, g⟩ ↦ ⟨0, 0, 0, d, g + 2 * d + 2, g + 1⟩) ⟨0, 0⟩
  intro ⟨d, g⟩
  exact ⟨⟨d + 1, g + d + 1⟩, main_trans d g⟩

end Sz22_2003_unofficial_657
