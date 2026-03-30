import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #783: [35/6, 55/2, 8/77, 39/5, 7/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  1  0  1  0
 3  0  0 -1 -1  0
 0  1 -1  0  0  1
 0  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_783

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d+1, e, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b e f,
    ⟨0, b, k, 0, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e (f + 1))
    ring_nf; finish

theorem r5_r3 : ⟨0, b, 0, 0, E + 1, F + 1⟩ [fm]⊢⁺ ⟨3, b, 0, 0, E, F⟩ := by
  step fm; step fm; finish

theorem r1r1r1_r3 : ⟨3, B + 3, C, D, E + 1, F⟩ [fm]⊢* ⟨3, B, C + 3, D + 2, E, F⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem r1r3_chain : ∀ j, ∀ C D E F,
    ⟨3, 3 * j, C, D, E + j, F⟩ [fm]⊢* ⟨3, 0, C + 3 * j, D + 2 * j, E, F⟩ := by
  intro j; induction' j with j ih <;> intro C D E F
  · simp; exists 0
  · rw [show 3 * (j + 1) = 3 * j + 3 from by ring,
        show E + (j + 1) = (E + j) + 1 from by ring]
    apply stepStar_trans (@r1r1r1_r3 (3 * j) C D (E + j) F)
    show ⟨3, 3 * j, C + 3, D + 2, E + j, F⟩ [fm]⊢*
      ⟨3, 0, C + (3 * j + 3), D + 2 * (j + 1), E, F⟩
    rw [show C + (3 * j + 3) = (C + 3) + 3 * j from by ring,
        show D + 2 * (j + 1) = (D + 2) + 2 * j from by ring]
    exact ih (C + 3) (D + 2) E F

theorem r2_triple : ⟨3, 0, C, D, E, F⟩ [fm]⊢⁺ ⟨0, 0, C + 3, D, E + 3, F⟩ := by
  step fm; step fm; step fm; finish

theorem r3_r2_chain : ∀ D, ∀ C E F,
    ⟨0, 0, C, D, E + 1, F⟩ [fm]⊢* ⟨0, 0, C + 3 * D, 0, E + 2 * D + 1, F⟩ := by
  intro D; induction' D with D ih <;> intro C E F
  · simp; exists 0
  · step fm
    step fm; step fm; step fm
    rw [show E + 3 = (E + 2) + 1 from by ring]
    apply stepStar_trans (ih (C + 3) (E + 2) F)
    ring_nf; finish

theorem inner_loop : ∀ q, ∀ E G,
    ⟨3, 3 * q, 0, 0, E + q, G⟩ [fm]⊢* ⟨0, 0, 9 * q + 3, 0, E + 4 * q + 3, G⟩ := by
  intro q E G
  apply stepStar_trans (r1r3_chain q 0 0 E G)
  rw [show 0 + 3 * q = 3 * q from by ring,
      show 0 + 2 * q = 2 * q from by ring]
  apply stepStar_trans (stepPlus_stepStar r2_triple)
  rw [show E + 3 = (E + 2) + 1 from by ring]
  apply stepStar_trans (r3_r2_chain (2 * q) (3 * q + 3) (E + 2) G)
  have h1 : 3 * q + 3 + 3 * (2 * q) = 9 * q + 3 := by ring
  have h2 : E + 2 + 2 * (2 * q) + 1 = E + 4 * q + 3 := by ring
  rw [h1, h2]; finish

theorem main_transition (q E F : ℕ) (hq : q ≥ 2) :
    ⟨0, 0, 3 * q, 0, E + q + 1, F⟩ [fm]⊢⁺
    ⟨0, 0, 9 * q + 3, 0, E + 4 * q + 3, F + 3 * q - 1⟩ := by
  apply stepStar_stepPlus_stepPlus (r4_chain (3 * q) 0 (E + q + 1) F)
  rw [show 0 + 3 * q = 3 * q from by ring,
      show E + q + 1 = (E + q) + 1 from by ring,
      show F + 3 * q = (F + 3 * q - 1) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus r5_r3
  exact inner_loop q E (F + 3 * q - 1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 6, 0, 4, 0⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun s ↦ ∃ q E F, s = ⟨0, 0, 3 * q, 0, E + q + 1, F⟩ ∧ q ≥ 2)
  · intro s ⟨q, E, F, hs, hq⟩; subst hs
    refine ⟨⟨0, 0, 9 * q + 3, 0, E + 4 * q + 3, F + 3 * q - 1⟩, ?_, main_transition q E F hq⟩
    refine ⟨3 * q + 1, E + q + 1, F + 3 * q - 1, ?_, by omega⟩
    rw [show 3 * (3 * q + 1) = 9 * q + 3 from by ring,
        show (E + q + 1) + (3 * q + 1) + 1 = E + 4 * q + 3 from by ring]
  · exact ⟨2, 1, 0, by norm_num, by omega⟩
