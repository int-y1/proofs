import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1068: [5/6, 1/385, 28/5, 121/2, 45/11]

Vector representation:
```
-1 -1  1  0  0
 0  0 -1 -1 -1
 2  0 -1  1  0
-1  0  0  0  2
 0  2  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1068

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | _ => none

private theorem r4_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; exact ih d (e + 2)

private theorem r5r2_drain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, 0, k, e + 2 * k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring,
        show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    step fm; step fm
    exact ih (b + 2) e

private theorem inner_loop : ∀ k, ∀ j D B,
    ⟨(2 : ℕ), B + 2 * k, j, D, 0⟩ [fm]⊢* ⟨2, B, j + k, D + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro j D B
  · ring_nf; finish
  · rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
        show j + (k + 1) = (j + 1) + k from by ring,
        show D + (k + 1) = (D + 1) + k from by ring]
    step fm; step fm; step fm
    exact ih (j + 1) (D + 1) B

private theorem r3_drain : ∀ k, ∀ a d,
    ⟨a, (0 : ℕ), k, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · ring_nf; finish
  · rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm; exact ih (a + 2) (d + 1)

private theorem opening (d : ℕ) :
    ⟨(0 : ℕ), 2 * d, 0, 0, 2⟩ [fm]⊢* ⟨2, 2 * d, 0, 1, 0⟩ := by
  step fm
  show ⟨0, 2 * d + 2, 1, 0, 1⟩ [fm]⊢* ⟨2, 2 * d, 0, 1, 0⟩
  step fm
  show ⟨(2 : ℕ), 2 * d + 2, 0, 1, 1⟩ [fm]⊢* ⟨2, 2 * d, 0, 1, 0⟩
  step fm; step fm; step fm; step fm
  ring_nf; finish

private theorem main_trans (d : ℕ) :
    ⟨d + 1, (0 : ℕ), 0, d, 0⟩ [fm]⊢⁺ ⟨2 * d + 2, 0, 0, 2 * d + 1, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨(d + 1 : ℕ), 0, 0, d, 0⟩ = some ⟨d, 0, 0, d, 2⟩
    rw [show d + 1 = d + 1 from rfl]; rfl
  apply stepStar_trans
  · show ⟨d, (0 : ℕ), 0, d, 2⟩ [fm]⊢* ⟨0, 0, 0, d, 2 + 2 * d⟩
    exact r4_drain d d 2
  rw [show (2 : ℕ) + 2 * d = 2 * d + 2 from by ring]
  apply stepStar_trans
  · show ⟨(0 : ℕ), 0, 0, d, 2 * d + 2⟩ [fm]⊢* ⟨0, 2 * d, 0, 0, 2⟩
    have h := r5r2_drain d 0 2
    convert h using 2; ring_nf
  apply stepStar_trans
  · exact opening d
  apply stepStar_trans
  · show ⟨(2 : ℕ), 2 * d, 0, 1, 0⟩ [fm]⊢* ⟨2, 0, d, d + 1, 0⟩
    have h := inner_loop d 0 1 0
    convert h using 2; ring_nf
  show ⟨(2 : ℕ), 0, d, d + 1, 0⟩ [fm]⊢* ⟨2 * d + 2, 0, 0, 2 * d + 1, 0⟩
  have h := r3_drain d 2 (d + 1)
  convert h using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨d + 1, 0, 0, d, 0⟩) 1
  intro d; exists 2 * d + 1; exact main_trans d

end Sz22_2003_unofficial_1068
