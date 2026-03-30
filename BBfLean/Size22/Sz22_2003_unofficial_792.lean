import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #792: [35/6, 605/2, 4/77, 3/5, 10/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_792

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem c_to_b : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem spiral_rounds : ∀ k, ⟨0, b + 2 * k, c, d + 1, e + k⟩ [fm]⊢*
    ⟨0, b, c + 2 * k, d + k + 1, e⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    rw [show (b + 2 * k) + 1 = (b + 2 * k + 1) + 0 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (c := c + 2) (d := d + 1) (e := e))
    ring_nf; finish

theorem drain : ∀ k, ⟨0, 0, c, d + k, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e + 1 + 3 * k⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (c := c + 2) (d := d) (e := e + 3))
    ring_nf; finish

theorem main_trans : ⟨0, 0, 2 * (m + 1), 0, m + 2 + f⟩ [fm]⊢⁺
    ⟨0, 0, 4 * m + 6, 0, 3 * m + f + 5⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * (m + 1) = 0 + 2 * (m + 1) from by ring]
    exact c_to_b (2 * (m + 1)) (b := 0) (c := 0) (e := m + 2 + f)
  rw [show (0 + 2 * (m + 1) : ℕ) = (2 * m + 1) + 1 from by ring,
      show m + 2 + f = (m + 1 + f) + 1 from by ring]
  step fm
  rw [show (2 * m + 1) + 1 = (2 * m + 1) + 1 from rfl]
  step fm
  rw [show (2 * m + 1 : ℕ) = 1 + 2 * m from by ring,
      show (m + 1 + f : ℕ) = (f + 1) + m from by ring]
  apply stepStar_trans (spiral_rounds m (b := 1) (c := 2) (d := 0) (e := f + 1))
  rw [show 2 + 2 * m = (2 * m + 2 : ℕ) from by ring,
      show 0 + m + 1 = (m + 1 : ℕ) from by ring]
  step fm
  step fm
  step fm
  show ⟨0, 0, 2 * m + 4, m + 1, f + 2⟩ [fm]⊢* ⟨0, 0, 4 * m + 6, 0, 3 * m + f + 5⟩
  rw [show (m + 1 : ℕ) = 0 + (m + 1) from by ring,
      show f + 2 = (f + 1) + 1 from by ring]
  apply stepStar_trans (drain (m + 1) (c := 2 * m + 4) (d := 0) (e := f + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 4⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m f, q = ⟨0, 0, 2 * (m + 1), 0, m + 2 + f⟩)
  · intro q ⟨m, f, hq⟩; subst hq
    refine ⟨⟨0, 0, 4 * m + 6, 0, 3 * m + f + 5⟩,
      ⟨2 * m + 2, m + f + 1, by ring_nf⟩, main_trans⟩
  · exact ⟨1, 1, by ring_nf⟩
