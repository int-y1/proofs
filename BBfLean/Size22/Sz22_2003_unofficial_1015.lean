import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1015: [4/15, 99/14, 25/2, 7/11, 14/5]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1015

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ c d,
    ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a c e,
    ⟨a + k, (0 : ℕ), c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) e)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, (0 : ℕ), c + 2 * k, k, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) c (e + 1))
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 2 * (n + 1) ^ 2 + 3 * (n + 1) + 2, 0, n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (n + 2) ^ 2 + 3 * (n + 2) + 2, 0, n + 2⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 2 * (n + 1) ^ 2 + 3 * (n + 1) + 2, 0, n + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * (n + 1) ^ 2 + 3 * (n + 1) + 2, n + 1, 0⟩ := by
    have := r4_chain (n + 1) (2 * (n + 1) ^ 2 + 3 * (n + 1) + 2) 0
    rw [show (0 : ℕ) + (n + 1) = n + 1 from by ring] at this; exact this
  have h2 : ⟨(0 : ℕ), 0, 2 * (n + 1) ^ 2 + 3 * (n + 1) + 2, n + 1, 0⟩ [fm]⊢⁺
      ⟨1, 0, 2 * n ^ 2 + 5 * n + 2 + 2 * (n + 2), n + 2, 0⟩ := by
    rw [show 2 * (n + 1) ^ 2 + 3 * (n + 1) + 2 =
        (2 * n ^ 2 + 5 * n + 2 + 2 * (n + 2)) + 1 from by ring]
    step fm; finish
  have h3 : ⟨(1 : ℕ), 0, 2 * n ^ 2 + 5 * n + 2 + 2 * (n + 2), n + 2, 0⟩ [fm]⊢*
      ⟨3 * (n + 2) + 1, 0, 2 * n ^ 2 + 5 * n + 2, 0, n + 2⟩ := by
    have := r2r1r1_chain (n + 2) 0 (2 * n ^ 2 + 5 * n + 2) 0
    rw [show (0 : ℕ) + 1 = 1 from by ring,
        show (0 : ℕ) + 3 * (n + 2) + 1 = 3 * (n + 2) + 1 from by ring,
        show (0 : ℕ) + (n + 2) = n + 2 from by ring] at this; exact this
  have h4 : ⟨3 * (n + 2) + 1, (0 : ℕ), 2 * n ^ 2 + 5 * n + 2, 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, 2 * (n + 2) ^ 2 + 3 * (n + 2) + 2, 0, n + 2⟩ := by
    have := r3_chain (3 * (n + 2) + 1) 0 (2 * n ^ 2 + 5 * n + 2) (n + 2)
    rw [show (0 : ℕ) + (3 * (n + 2) + 1) = 3 * (n + 2) + 1 from by ring,
        show 2 * n ^ 2 + 5 * n + 2 + 2 * (3 * (n + 2) + 1) =
            2 * (n + 2) ^ 2 + 3 * (n + 2) + 2 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 7, 0, 1⟩) (by execute fm 9)
  have : (⟨0, 0, 7, 0, 1⟩ : Q) =
      ⟨0, 0, 2 * (0 + 1) ^ 2 + 3 * (0 + 1) + 2, 0, 0 + 1⟩ := by norm_num
  rw [this]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * (n + 1) ^ 2 + 3 * (n + 1) + 2, 0, n + 1⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
