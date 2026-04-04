import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1806: [9/10, 55/21, 2/3, 7/11, 165/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1806

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k a d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

theorem b_to_a : ∀ k a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) e)
    ring_nf; finish

theorem r2r1_chain : ∀ k a b d e, ⟨a + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    ring_nf; finish

theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, n + 2⟩ := by
  have h1 : ⟨n + 2, 0, 0, 0, n + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, n + 1, 0⟩ := by
    have := e_to_d (n + 1) (n + 2) 0
    rw [show (0 : ℕ) + (n + 1) = n + 1 from by omega] at this
    exact this
  have h2 : ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨n, 3, 0, n + 1, 1⟩ := by
    step fm; step fm; finish
  have h3 : ⟨n, 3, 0, n + 1, 1⟩ [fm]⊢* ⟨0, n + 3, 0, 1, n + 1⟩ := by
    have := r2r1_chain n 0 2 1 1
    rw [show (0 : ℕ) + n = n from by omega,
        show (2 : ℕ) + 1 = 3 from by omega,
        show (1 : ℕ) + n = n + 1 from by omega,
        show 2 + n + 1 = n + 3 from by omega] at this
    exact this
  have h4 : ⟨0, n + 3, 0, 1, n + 1⟩ [fm]⊢⁺ ⟨0, n + 3, 0, 0, n + 2⟩ := by
    step fm; step fm; step fm; finish
  have h5 : ⟨0, n + 3, 0, 0, n + 2⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, n + 2⟩ := by
    have := b_to_a (n + 3) 0 (n + 2)
    rw [show (0 : ℕ) + (n + 3) = n + 3 from by omega] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_trans h2
      (stepStar_stepPlus_stepPlus h3
        (stepPlus_stepStar_stepPlus h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, n + 1⟩) 0
  intro n; exists n + 1; exact main_trans n
