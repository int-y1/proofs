import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1900: [9/35, 65/33, 14/3, 11/13, 273/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1900

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d+1, e, f+1⟩
  | _ => none

theorem r2r1_chain : ∀ e B, ⟨A, B + 1, 0, B + 2 * e + 1, e, B + 1⟩ [fm]⊢*
    ⟨A, B + e + 1, 0, B + e + 1, 0, B + e + 1⟩ := by
  intro e; induction' e with e ih
  · intro B; exists 0
  · intro B
    step fm
    step fm
    show ⟨A, B + 2, 0, B + 2 * (e + 1), e, B + 1 + 1⟩ [fm]⊢*
      ⟨A, B + (e + 1) + 1, 0, B + (e + 1) + 1, 0, B + (e + 1) + 1⟩
    rw [show B + 2 = (B + 1) + 1 from by ring,
        show B + 2 * (e + 1) = (B + 1) + 2 * e + 1 from by ring,
        show B + 1 + 1 = (B + 1) + 1 from by ring,
        show B + (e + 1) + 1 = (B + 1) + e + 1 from by ring]
    exact ih (B + 1)

theorem r3_chain : ∀ k A D F, ⟨A, k, 0, D, 0, F⟩ [fm]⊢* ⟨A + k, 0, 0, D + k, 0, F⟩ := by
  intro k; induction' k with k ih
  · intro A D F; exists 0
  · intro A D F
    step fm
    apply stepStar_trans (ih (A + 1) (D + 1) F)
    ring_nf; finish

theorem r4_chain : ∀ k A D E, ⟨A, 0, 0, D, E, k⟩ [fm]⊢* ⟨A, 0, 0, D, E + k, 0⟩ := by
  intro k; induction' k with k ih
  · intro A D E; exists 0
  · intro A D E
    step fm
    apply stepStar_trans (ih A D (E + 1))
    ring_nf; finish

theorem main_trans : ∀ n, ⟨A + 1, 0, 0, 2 * n, n, 0⟩ [fm]⊢⁺
    ⟨A + n + 1, 0, 0, 2 * (n + 1), n + 1, 0⟩ := by
  intro n
  step fm
  show ⟨A, 1, 0, 2 * n + 1, n, 1⟩ [fm]⊢* ⟨A + n + 1, 0, 0, 2 * (n + 1), n + 1, 0⟩
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * n + 1 = 0 + 2 * n + 1 from by ring]
  apply stepStar_trans (r2r1_chain n 0 (A := A))
  rw [show 0 + n + 1 = n + 1 from by ring]
  apply stepStar_trans (r3_chain (n + 1) A (n + 1) (n + 1))
  rw [show n + 1 + (n + 1) = 2 * (n + 1) from by ring]
  apply stepStar_trans (r4_chain (n + 1) (A + (n + 1)) (2 * (n + 1)) 0)
  rw [show A + (n + 1) = A + n + 1 from by ring]
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0 + 1, 0, 0, 2 * 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, n⟩ ↦ ⟨F + 1, 0, 0, 2 * n, n, 0⟩) ⟨0, 0⟩
  intro ⟨F, n⟩; exact ⟨⟨F + n, n + 1⟩, main_trans n⟩
