import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1027: [4/15, 99/14, 65/2, 7/11, 22/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  2  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 1  0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1027

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c e f,
    ⟨a + k, (0 : ℕ), c, 0, e, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d f,
    ⟨(0 : ℕ), 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ j c d f,
    ⟨3 * j + 1, (0 : ℕ), c + 2 * k, d + k, j + 1, f⟩ [fm]⊢*
    ⟨3 * (j + k) + 1, 0, c, d, j + k + 1, f⟩ := by
  intro k; induction' k with k ih <;> intro j c d f
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show 3 * (j + (k + 1)) + 1 = 3 * ((j + 1) + k) + 1 from by ring,
        show j + (k + 1) + 1 = (j + 1) + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (j + 1) c d f)
    ring_nf; finish

theorem main_trans (c e f : ℕ) :
    ⟨3 * e + 4, (0 : ℕ), c, 0, e + 2, f⟩ [fm]⊢⁺
    ⟨3 * (e + 1) + 4, 0, c + e, 0, (e + 1) + 2, f + 3 * e + 3⟩ := by
  have h1 : ⟨3 * e + 4, (0 : ℕ), c, 0, e + 2, f⟩ [fm]⊢*
      ⟨0, 0, c + 3 * e + 4, 0, e + 2, f + 3 * e + 4⟩ := by
    rw [show 3 * e + 4 = 0 + (3 * e + 4) from by ring]
    have := r3_chain (3 * e + 4) 0 c (e + 2) f
    rw [show c + (3 * e + 4) = c + 3 * e + 4 from by ring,
        show f + (3 * e + 4) = f + 3 * e + 4 from by ring] at this; exact this
  have h2 : ⟨(0 : ℕ), 0, c + 3 * e + 4, 0, e + 2, f + 3 * e + 4⟩ [fm]⊢*
      ⟨0, 0, c + 3 * e + 4, e + 2, 0, f + 3 * e + 4⟩ := by
    have := r4_chain (e + 2) (c + 3 * e + 4) 0 (f + 3 * e + 4)
    rw [show (0 : ℕ) + (e + 2) = e + 2 from by ring] at this; exact this
  have h3 : ⟨(0 : ℕ), 0, c + 3 * e + 4, e + 2, 0, f + 3 * e + 4⟩ [fm]⊢⁺
      ⟨1, 0, c + 3 * e + 4, e + 2, 1, f + 3 * e + 3⟩ := by
    rw [show f + 3 * e + 4 = (f + 3 * e + 3) + 1 from by ring]
    step fm; finish
  have h4 : ⟨(1 : ℕ), 0, c + 3 * e + 4, e + 2, 1, f + 3 * e + 3⟩ [fm]⊢*
      ⟨3 * (e + 1) + 4, 0, c + e, 0, (e + 1) + 2, f + 3 * e + 3⟩ := by
    have := r2r1r1_chain (e + 2) 0 (c + e) 0 (f + 3 * e + 3)
    rw [show 3 * (0 : ℕ) + 1 = 1 from by ring,
        show (c + e) + 2 * (e + 2) = c + 3 * e + 4 from by ring,
        show (0 : ℕ) + (e + 2) = e + 2 from by ring] at this
    rw [show 3 * (e + 2) + 1 = 3 * (e + 1) + 4 from by ring,
        show e + 2 + 1 = (e + 1) + 2 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 2, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨c, e, f⟩ ↦ ⟨3 * e + 4, 0, c, 0, e + 2, f⟩) ⟨0, 0, 0⟩
  intro ⟨c, e, f⟩; exact ⟨⟨c + e, e + 1, f + 3 * e + 3⟩, main_trans c e f⟩
