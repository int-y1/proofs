import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1859: [9/35, 20/3, 1/20, 49/2, 9/7]

Vector representation:
```
 0  2 -1 -1
 2 -1  1  0
-2  0 -1  0
-1  0  0  2
 0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1859

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a+2, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | _ => none

-- Interleave: R2+R1 repeated m times.
theorem interleave : ∀ m, ⟨a, b + 2, 0, d + m⟩ [fm]⊢* ⟨a + 2 * m, b + m + 2, 0, d⟩ := by
  intro m; induction' m with m ih generalizing a b d
  · exists 0
  · rw [show d + (m + 1) = (d + m) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a + 2) (b := b + 1) (d := d))
    ring_nf; finish

-- R2 chain: (a, b+k, c, 0) →* (a+2*k, b, c+k, 0)
theorem r2_chain : ∀ k, ⟨a, b + k, c, 0⟩ [fm]⊢* ⟨a + 2 * k, b, c + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (b := b) (c := c + 1))
    ring_nf; finish

-- R3 chain: (a+2*k, 0, c+k, 0) →* (a, 0, c, 0)
theorem r3_chain : ∀ k, ⟨a + 2 * k, 0, c + k, 0⟩ [fm]⊢* ⟨a, 0, c, 0⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (a := a + 2) (c := c + 1))
    step fm
    finish

-- R4 chain: (a+k, 0, 0, d) →* (a, 0, 0, d+2*k)
theorem r4_chain : ∀ k, ⟨a + k, 0, 0, d⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring]
    apply stepStar_trans (ih (a := a + 1) (d := d))
    step fm
    ring_nf; finish

-- Interleave starting from natural form after R5.
theorem interleave_from (n : ℕ) : ⟨0, 2, 0, 2 * n + 1⟩ [fm]⊢* ⟨4 * n + 2, 2 * n + 3, 0, 0⟩ := by
  rw [show (2 : ℕ) = 0 + 2 from by ring, show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
  apply stepStar_trans (interleave (2 * n + 1) (a := 0) (b := 0) (d := 0))
  ring_nf; finish

-- Phase composition: (0, 2, 0, 2*n+1) →* (0, 0, 0, 8*n+4)
theorem phases (n : ℕ) : ⟨0, 2, 0, 2 * n + 1⟩ [fm]⊢* ⟨0, 0, 0, 8 * n + 4⟩ := by
  apply stepStar_trans (interleave_from n)
  rw [show 2 * n + 3 = 0 + (2 * n + 3) from by ring]
  apply stepStar_trans (r2_chain (2 * n + 3) (a := 4 * n + 2) (b := 0) (c := 0))
  rw [show 4 * n + 2 + 2 * (2 * n + 3) = (4 * n + 2) + 2 * (2 * n + 3) from by ring,
      show (0 : ℕ) + (2 * n + 3) = 0 + (2 * n + 3) from by ring]
  apply stepStar_trans (r3_chain (2 * n + 3) (a := 4 * n + 2) (c := 0))
  rw [show 4 * n + 2 = 0 + (4 * n + 2) from by ring]
  apply stepStar_trans (r4_chain (4 * n + 2) (a := 0) (d := 0))
  ring_nf; finish

-- Main transition: (0, 0, 0, 2*(n+1)) →⁺ (0, 0, 0, 8*n+4)
theorem main_trans (n : ℕ) : ⟨0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 8 * n + 4⟩ := by
  apply step_stepStar_stepPlus
    (show fm ⟨0, 0, 0, 2 * n + 2⟩ = some ⟨0, 2, 0, 2 * n + 1⟩ from by
      simp [fm])
  exact phases n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 2⟩) 0
  intro n
  refine ⟨4 * n + 1, ?_⟩
  rw [show 2 * (4 * n + 1) + 2 = 8 * n + 4 from by ring]
  exact main_trans n
