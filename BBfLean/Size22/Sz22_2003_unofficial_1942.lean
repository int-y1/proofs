import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1942: [9/70, 4/33, 55/2, 7/11, 33/5]

Vector representation:
```
-1  2 -1 -1  0
 2 -1  0  0 -1
-1  0  1  0  1
 0  0  0  1 -1
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1942

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R3 chain: (n, 0, c, 0, j) →* (0, 0, c+n, 0, j+n)
theorem r3_chain : ∀ n, ⟨n, 0, c, 0, j⟩ [fm]⊢* ⟨0, 0, c + n, 0, j + n⟩ := by
  intro n; induction' n with n ih generalizing c j
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 1) (j := j + 1))
    ring_nf; finish

-- R4 chain: (0, 0, C, d, n) →* (0, 0, C, d+n, 0)
theorem r4_chain : ∀ n, ⟨0, 0, C, d, n⟩ [fm]⊢* ⟨0, 0, C, d + n, 0⟩ := by
  intro n; induction' n with n ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- Drain: (0, b, 3k+2+F, 2k+1, 0) →* (1, b+4k+2, F, 0, 0)
theorem drain : ∀ k, ∀ b F, ⟨0, b, 3 * k + 2 + F, 2 * k + 1, 0⟩ [fm]⊢* ⟨1, b + 4 * k + 2, F, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b F
  · rw [show 3 * 0 + 2 + F = F + 1 + 1 from by ring,
        show 2 * 0 + 1 = 0 + 1 from by ring]
    step fm; step fm; step fm
    rw [show b + 4 * 0 + 2 = b + 2 from by ring]
    finish
  · rw [show 3 * (k + 1) + 2 + F = (3 * k + 2 + F) + 2 + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (b := b + 4) F)
    rw [show b + 4 + 4 * k + 2 = b + 4 * (k + 1) + 2 from by ring]
    finish

-- R3+R2 chain: (j+1, B, c', 0, 0) →* (j+1+B, 0, c'+B, 0, 0)
theorem r3r2_chain : ∀ B, ∀ j c', ⟨j + 1, B, c', 0, 0⟩ [fm]⊢* ⟨j + 1 + B, 0, c' + B, 0, 0⟩ := by
  intro B; induction' B with B ih <;> intro j c'
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (j := j + 1) (c' := c' + 1))
    ring_nf; finish

-- One R3 step on symbolic state
theorem r3_step : ⟨a + 1, 0, c, 0, e⟩ [fm]⊢ ⟨a, 0, c + 1, 0, e + 1⟩ := by simp [fm]

-- Main transition: (2k+1, 0, k+1+F, 0, 0) →⁺ (4k+3, 0, 4k+2+F, 0, 0)
theorem main_trans : ⟨2 * k + 1, 0, k + 1 + F, 0, 0⟩ [fm]⊢⁺ ⟨4 * k + 3, 0, 4 * k + 2 + F, 0, 0⟩ := by
  rw [show 2 * k + 1 = 2 * k + 0 + 1 from by ring]
  apply step_stepStar_stepPlus (r3_step (a := 2 * k + 0) (c := k + 1 + F) (e := 0))
  show ⟨2 * k + 0, 0, k + 1 + F + 1, 0, 0 + 1⟩ [fm]⊢* ⟨4 * k + 3, 0, 4 * k + 2 + F, 0, 0⟩
  apply stepStar_trans (r3_chain (2 * k + 0) (c := k + 1 + F + 1) (j := 0 + 1))
  rw [show k + 1 + F + 1 + (2 * k + 0) = 3 * k + 2 + F from by ring,
      show 0 + 1 + (2 * k + 0) = 2 * k + 1 from by ring]
  apply stepStar_trans (r4_chain (2 * k + 1) (C := 3 * k + 2 + F) (d := 0))
  rw [show (0 : ℕ) + (2 * k + 1) = 2 * k + 1 from by ring]
  apply stepStar_trans (drain k 0 F)
  rw [show (0 : ℕ) + 4 * k + 2 = 4 * k + 2 from by ring]
  apply stepStar_trans (r3r2_chain (4 * k + 2) 0 F)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 5, 0, 0⟩) (by execute fm 34)
  show ¬halts fm (⟨2 * 3 + 1, 0, 3 + 1 + 1, 0, 0⟩ : Q)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, F⟩ ↦ ⟨2 * k + 1, 0, k + 1 + F, 0, 0⟩) ⟨3, 1⟩
  intro ⟨k, F⟩
  refine ⟨⟨2 * k + 1, 2 * k + F⟩, ?_⟩
  show ⟨2 * k + 1, 0, k + 1 + F, 0, 0⟩ [fm]⊢⁺ ⟨2 * (2 * k + 1) + 1, 0, (2 * k + 1) + 1 + (2 * k + F), 0, 0⟩
  rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring,
      show (2 * k + 1) + 1 + (2 * k + F) = 4 * k + 2 + F from by ring]
  exact main_trans
