import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1733: [8/15, 33/14, 5/2, 7/11, 28/5]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1733

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

theorem e_to_d : ∀ k, ∀ d, ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih (d + 1)

theorem a_to_c : ∀ k, ∀ c, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c e, ⟨a + 2, 0, c + 1 + k, k + 1, e⟩ [fm]⊢* ⟨a + 2 * k + 4, 0, c, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · step fm; step fm; ring_nf; finish
  · rw [show c + 1 + (k + 1) = c + 1 + k + 1 from by ring,
        show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring]
    step fm
    step fm
    rw [show a + 2 * (k + 1) + 4 = (a + 2) + 2 * k + 4 from by ring,
        show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring]
    exact ih (a + 2) c (e + 1)

theorem spiral : ⟨0, 0, f + d + 3, d + 1, 0⟩ [fm]⊢⁺ ⟨2 * d + 6, 0, f, 0, d + 2⟩ := by
  rw [show f + d + 3 = f + 1 + (d + 1) + 1 from by ring]
  step fm
  show ⟨2, 0, f + 1 + (d + 1), (d + 1) + 1, 0⟩ [fm]⊢* ⟨2 * d + 6, 0, f, 0, d + 2⟩
  rw [show f + 1 + (d + 1) = f + 1 + d + 1 from by ring]
  apply stepStar_trans (r2r1_chain (d + 1) 0 f 0)
  rw [show 0 + 2 * (d + 1) + 4 = 2 * d + 6 from by ring,
      show 0 + (d + 1) + 1 = d + 2 from by ring]
  finish

theorem main_trans : ⟨0, 0, f + d + 3, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, f + 2 * d + 6, d + 2, 0⟩ := by
  apply stepPlus_stepStar_stepPlus spiral
  apply stepStar_trans (a_to_c (2 * d + 6) (c := f) (e := d + 2))
  rw [show f + (2 * d + 6) = f + 2 * d + 6 from by ring]
  apply stepStar_trans (e_to_d (d + 2) (c := f + 2 * d + 6) (d := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 1, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨f, d⟩ ↦ ⟨0, 0, f + d + 3, d + 1, 0⟩) ⟨0, 0⟩
  intro ⟨f, d⟩
  refine ⟨⟨f + d + 2, d + 1⟩, ?_⟩
  show ⟨0, 0, f + d + 3, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, (f + d + 2) + (d + 1) + 3, (d + 1) + 1, 0⟩
  rw [show (f + d + 2) + (d + 1) + 3 = f + 2 * d + 6 from by ring,
      show (d + 1) + 1 = d + 2 from by ring]
  exact main_trans
