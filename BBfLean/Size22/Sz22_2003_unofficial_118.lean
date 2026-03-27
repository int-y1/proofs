import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #118: [1/4, 45/2, 2/21, 11/3, 7/55, 2/11]

Vector representation:
```
-2  0  0  0  0
-1  2  1  0  0
 1 -1  0 -1  0
 0 -1  0  0  1
 0  0 -1  1 -1
 1  0  0  0 -1
```

This Fractran program doesn't halt. Starting from (1,0,0,0,0), it reaches
(1,0,0,1,0) and then cycles through (1,0,0,d,0) with d increasing by 1
each iteration.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_118

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R3/R2 interleaved: each pair does b→b+1, c→c+1, d→d-1
theorem r3r2_chain : ∀ k, ∀ b c, ⟨0, b+1, c, k, 0⟩ [fm]⊢* ⟨0, b+1+k, c+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih (b+1) (c+1))
  ring_nf; finish

-- R4 phase: convert b to e (d=0, accumulate e)
theorem b_to_e : ∀ k, ∀ e, ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  step fm
  apply stepStar_trans (ih (e+1))
  ring_nf; finish

-- R5 phase: convert c and e to d (accumulate d)
theorem ce_to_d : ∀ k, ∀ c d e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih c (d+1) e)
  ring_nf; finish

-- Main cycle: (1, 0, 0, d, 0) →⁺ (1, 0, 0, d+1, 0)
theorem main_cycle (d : ℕ) : ⟨1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, d+1, 0⟩ := by
  -- R2: (1, 0, 0, d, 0) → (0, 2, 1, d, 0)
  step fm
  -- R3/R2 chain: (0, 2, 1, d, 0) = (0, 1+1, 1, d, 0) →* (0, 1+1+d, 1+d, 0, 0) = (0, d+2, d+1, 0, 0)
  apply stepStar_trans (r3r2_chain d 1 1)
  -- R4 phase: (0, d+2, d+1, 0, 0) →* (0, 0, d+1, 0, d+2)
  rw [show 1 + 1 + d = d + 2 from by ring, show 1 + d = d + 1 from by ring]
  apply stepStar_trans (b_to_e (d+2) 0)
  -- R5 phase: (0, 0, d+1, 0, d+2) →* (0, 0, 0, d+1, 1)
  simp only [Nat.zero_add]
  rw [show d + 1 = 0 + (d + 1) from by ring,
      show d + 2 = 1 + (d + 1) from by ring]
  apply stepStar_trans (ce_to_d (d+1) 0 0 1)
  simp only [Nat.zero_add]
  -- Now at (0, 0, 0, d+1, 1). R6: (0, 0, 0, d+1, 1) → (1, 0, 0, d+1, 0)
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 0⟩)
  · execute fm 5
  exact progress_nonhalt_simple (fm := fm) (A := ℕ) (C := fun d ↦ ⟨1, 0, 0, d, 0⟩)
    1 (fun d ↦ ⟨d+1, main_cycle d⟩)
