import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1007: [4/15, 7203/2, 1/147, 5/7, 3/5]

Vector representation:
```
 2 -1 -1  0
-1  1  0  4
 0 -1  0 -2
 0  0  1 -1
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1007

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c, d+4⟩
  | ⟨a, b+1, c, d+2⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

theorem d_to_c : ∀ k, ∀ c, ⟨0, 0, c, k⟩ [fm]⊢* ⟨0, 0, c + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · ring_nf; finish
  · step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d,
    ⟨a + 1, 0, c + k, d⟩ [fm]⊢* ⟨a + k + 1, 0, c, d + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (d + 4))
    ring_nf; finish

theorem r2_pure_chain : ∀ k, ∀ a b d,
    ⟨a + k, b, 0, d⟩ [fm]⊢* ⟨a, b + k, 0, d + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (d + 4))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ d,
    ⟨0, k, 0, d + 2 * k⟩ [fm]⊢* ⟨0, 0, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro d
  · ring_nf; finish
  · rw [show d + 2 * (k + 1) = d + 2 * k + 2 from by ring]
    step fm
    exact ih d

theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 6 * n + 4, 0⟩ := by
  have h1 : ⟨0, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨2, 0, n, 0⟩ := by
    rw [show n + 2 = n + 1 + 1 from by ring]
    step fm; step fm; finish
  have h2 : ⟨2, 0, n, 0⟩ [fm]⊢* ⟨n + 2, 0, 0, 4 * n⟩ := by
    have := r2r1_chain n 1 0 0
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show (0 : ℕ) + n = n from by ring,
        show 1 + n + 1 = n + 2 from by ring,
        show (0 : ℕ) + 4 * n = 4 * n from by ring] at this; exact this
  have h3 : ⟨n + 2, 0, 0, 4 * n⟩ [fm]⊢* ⟨0, n + 2, 0, 8 * n + 8⟩ := by
    have := r2_pure_chain (n + 2) 0 0 (4 * n)
    rw [show (0 : ℕ) + (n + 2) = n + 2 from by ring,
        show 4 * n + 4 * (n + 2) = 8 * n + 8 from by ring] at this; exact this
  have h4 : ⟨0, n + 2, 0, 8 * n + 8⟩ [fm]⊢* ⟨0, 0, 0, 6 * n + 4⟩ := by
    have := r3_chain (n + 2) (6 * n + 4)
    rw [show 6 * n + 4 + 2 * (n + 2) = 8 * n + 8 from by ring] at this; exact this
  have h5 : ⟨0, 0, 0, 6 * n + 4⟩ [fm]⊢* ⟨0, 0, 6 * n + 4, 0⟩ := by
    have := d_to_c (6 * n + 4) 0
    rw [show (0 : ℕ) + (6 * n + 4) = 6 * n + 4 from by ring] at this; exact this
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0⟩) 0
  intro n; exact ⟨6 * n + 2, main_trans n⟩
