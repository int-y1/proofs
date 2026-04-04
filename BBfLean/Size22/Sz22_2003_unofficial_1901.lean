import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1901: [9/35, 65/33, 14/3, 11/13, 385/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  0  1  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1901

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | _ => none

theorem r1r2_chain : ∀ E, ⟨A, k, 1, E + 1 + G, E, F⟩ [fm]⊢* ⟨A, k + E + 2, 0, G, 0, F + E⟩ := by
  intro E; induction' E with E ih generalizing k F G
  · rw [show (0 : ℕ) + 1 + G = G + 1 from by ring]
    apply step_stepStar
    show fm ⟨A, k, 0 + 1, G + 1, 0, F⟩ = some ⟨A, k + 2, 0, G, 0, F⟩
    simp [fm]
  · rw [show E + 1 + 1 + G = (E + 1 + G) + 1 from by ring]
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A, k, 1, (E + 1 + G) + 1, E + 1, F⟩ [fm]⊢ ⟨A, k + 2, 0, E + 1 + G, E + 1, F⟩))
    apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A, k + 2, 0, E + 1 + G, E + 1, F⟩ [fm]⊢ ⟨A, k + 1, 1, E + 1 + G, E, F + 1⟩))
    apply stepStar_trans (ih (k := k + 1) (F := F + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨A, k, 0, D, 0, F⟩ [fm]⊢* ⟨A + k, 0, 0, D + k, 0, F⟩ := by
  intro k; induction' k with k ih generalizing A D
  · exists 0
  · apply stepStar_trans (step_stepStar (by simp [fm] : ⟨A, k + 1, 0, D, 0, F⟩ [fm]⊢ ⟨A + 1, k, 0, D + 1, 0, F⟩))
    apply stepStar_trans (ih (A := A + 1) (D := D + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨A, 0, 0, D, E, k⟩ [fm]⊢* ⟨A, 0, 0, D, E + k, 0⟩ := by
  intro k; induction' k with k ih generalizing E
  · exists 0
  · step fm
    apply stepStar_trans (ih (E := E + 1))
    ring_nf; finish

theorem main_trans : ⟨a + 3, 0, 0, 2 * e + 2, e + 1, 0⟩ [fm]⊢⁺ ⟨a + e + 6, 0, 0, 2 * e + 4, e + 2, 0⟩ := by
  rw [show a + 3 = (a + 2) + 1 from by ring]
  step fm
  rw [show 2 * e + 2 + 1 = (e + 2) + 1 + e from by ring,
      show e + 1 + 1 = e + 2 from by ring]
  apply stepStar_trans (r1r2_chain (e + 2) (A := a + 2) (k := 0) (G := e) (F := 0))
  rw [show 0 + (e + 2) + 2 = e + 4 from by ring,
      show 0 + (e + 2) = e + 2 from by ring]
  apply stepStar_trans (r3_chain (e + 4) (A := a + 2) (D := e) (F := e + 2))
  rw [show a + 2 + (e + 4) = a + e + 6 from by ring,
      show e + (e + 4) = 2 * e + 4 from by ring]
  apply stepStar_trans (r4_chain (e + 2) (A := a + e + 6) (D := 2 * e + 4) (E := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2, 1, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 3, 0, 0, 2 * e + 2, e + 1, 0⟩) ⟨0, 0⟩
  intro ⟨a, e⟩; exact ⟨⟨a + e + 3, e + 1⟩, main_trans⟩
