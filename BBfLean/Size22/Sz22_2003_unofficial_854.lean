import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #854: [36/35, 5/3, 1/10, 343/2, 10/7]

Vector representation:
```
 2  2 -1 -1
 0 -1  1  0
-1  0 -1  0
-1  0  0  3
 1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_854

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+2, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a+1, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+3⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b, c+1, d⟩
  | _ => none

-- R1+R2 chain: each round does R1 then R2.
theorem r1r2_chain : ∀ k, ∀ a b d, ⟨a, b, 1, k + d⟩ [fm]⊢* ⟨a + 2 * k, b + k, 1, d⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; finish
  · rw [show k + 1 + d = (k + d) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 2) (b + 1) d)
    ring_nf; finish

-- R2 drain: move b to c when d=0.
theorem b_to_c : ∀ k, ∀ a b c, ⟨a, k + b, c, 0⟩ [fm]⊢* ⟨a, b, c + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · simp; finish
  · rw [show k + 1 + b = (k + b) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (c + 1))
    ring_nf; finish

-- R3 drain: decrease a and c together (b=0, d=0).
theorem r3_drain : ∀ k, ∀ a c, ⟨k + a, 0, k + c, 0⟩ [fm]⊢* ⟨a, 0, c, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · simp; finish
  · rw [show k + 1 + a = (k + a) + 1 from by ring,
        show k + 1 + c = (k + c) + 1 from by ring]
    step fm
    exact ih a c

-- R4 drain: convert a to d (b=0, c=0).
theorem r4_drain : ∀ k, ∀ d, ⟨k, 0, 0, d⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · simp; finish
  · step fm
    apply stepStar_trans (ih (d + 3))
    ring_nf; finish

-- Main transition: (0, 0, 0, D+2) →⁺ (0, 0, 0, 3*D+3)
theorem main_trans : ⟨0, 0, 0, D + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * D + 3⟩ := by
  rw [show D + 2 = (D + 1) + 1 from by ring]
  step fm
  show ⟨1, 0, 1, D + 1⟩ [fm]⊢* ⟨0, 0, 0, 3 * D + 3⟩
  apply stepStar_trans (r1r2_chain D 1 0 1)
  show ⟨1 + 2 * D, 0 + D, 1, 1⟩ [fm]⊢* ⟨0, 0, 0, 3 * D + 3⟩
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  show ⟨1 + 2 * D + 2, 0 + D + 2, 0, 0⟩ [fm]⊢* ⟨0, 0, 0, 3 * D + 3⟩
  rw [show 0 + D + 2 = (D + 2) + 0 from by ring]
  apply stepStar_trans (b_to_c (D + 2) (1 + 2 * D + 2) 0 0)
  show ⟨1 + 2 * D + 2, 0, 0 + (D + 2), 0⟩ [fm]⊢* ⟨0, 0, 0, 3 * D + 3⟩
  rw [show 1 + 2 * D + 2 = (D + 2) + (D + 1) from by ring,
      show 0 + (D + 2) = (D + 2) + 0 from by ring]
  apply stepStar_trans (r3_drain (D + 2) (D + 1) 0)
  show ⟨D + 1, 0, 0, 0⟩ [fm]⊢* ⟨0, 0, 0, 3 * D + 3⟩
  apply stepStar_trans (r4_drain (D + 1) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2⟩) 1
  intro n
  exact ⟨3 * n + 1, by rw [show 3 * n + 1 + 2 = 3 * n + 3 from by ring]; exact main_trans⟩
