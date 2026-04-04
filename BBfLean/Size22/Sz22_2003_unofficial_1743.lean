import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1743: [8/15, 33/14, 65/2, 7/11, 33/13]

Vector representation:
```
 3 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1743

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

theorem e_to_d : ∀ k, ∀ C D F, ⟨0, 0, C, D, k, F⟩ [fm]⊢* ⟨0, 0, C, D + k, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro C D F
  · exists 0
  · rw [show D + (k + 1) = (D + 1) + k from by ring]
    step fm
    exact ih C (D + 1) F

theorem r3_drain : ∀ k, ∀ C E F, ⟨k, 0, C, 0, E, F⟩ [fm]⊢* ⟨0, 0, C + k, 0, E, F + k⟩ := by
  intro k; induction' k with k ih <;> intro C E F
  · exists 0
  · step fm
    apply stepStar_trans (ih (C + 1) E (F + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ A C E F, ⟨A + 1, 0, C + k, k, E, F⟩ [fm]⊢* ⟨A + 2 * k + 1, 0, C, 0, E + k, F⟩ := by
  intro k; induction' k with k ih <;> intro A C E F
  · exists 0
  · rw [show C + (k + 1) = (C + k) + 1 from by ring]
    step fm
    step fm
    rw [show A + 1 + 2 = (A + 2) + 1 from by ring]
    apply stepStar_trans (ih (A + 2) C (E + 1) F)
    ring_nf; finish

theorem main_trans (c e f : ℕ) :
    ⟨0, 0, c + e + 2, 0, e + 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * e + 5, 0, e + 2, f + 2 * e + 5⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_d (e + 1) (c + e + 2) 0 (f + 1))
  rw [show 0 + (e + 1) = e + 1 from by ring]
  step fm
  step fm
  show ⟨3, 0, c + e + 1, e + 1, 1, f⟩ [fm]⊢* ⟨0, 0, c + 2 * e + 5, 0, e + 2, f + 2 * e + 5⟩
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show c + e + 1 = c + (e + 1) from by ring]
  apply stepStar_trans (r2r1_chain (e + 1) 2 c 1 f)
  rw [show 2 + 2 * (e + 1) + 1 = 2 * e + 5 from by ring,
      show 1 + (e + 1) = e + 2 from by ring]
  apply stepStar_trans (r3_drain (2 * e + 5) c (e + 2) f)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 1, 3⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨c, e, f⟩ ↦ ⟨0, 0, c + e + 2, 0, e + 1, f + 1⟩) ⟨1, 0, 2⟩
  intro ⟨c, e, f⟩
  refine ⟨⟨c + e + 2, e + 1, f + 2 * e + 4⟩, ?_⟩
  show ⟨0, 0, c + e + 2, 0, e + 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, (c + e + 2) + (e + 1) + 2, 0, (e + 1) + 1, (f + 2 * e + 4) + 1⟩
  rw [show (c + e + 2) + (e + 1) + 2 = c + 2 * e + 5 from by ring,
      show (e + 1) + 1 = e + 2 from by ring,
      show (f + 2 * e + 4) + 1 = f + 2 * e + 5 from by ring]
  exact main_trans c e f
