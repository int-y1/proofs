import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #14: [1/12, 25/2, 6/35, 11/5, 196/11]

Vector representation:
```
-2 -1  0  0  0
-1  0  2  0  0
 1  1 -1 -1  0
 0  0 -1  0  1
 2  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_14

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | _ => none

theorem r3r2_chain : ∀ k, ∀ b c e, ⟨0, b, c + 1, k, e⟩ [fm]⊢* ⟨0, b + k, c + 1 + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  step fm; step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

theorem r4_chain : ∀ k, ∀ b e, ⟨0, b, k, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem r5r1_chain : ∀ k, ∀ d e, ⟨0, k, 0, d, e + k⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem main_trans : ∀ d e, ⟨0, 0, 0, d, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 4, e + 4⟩ := by
  intro d e
  step fm; step fm; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (d + 2) 0 3 e)
  rw [show 0 + (d + 2) = d + 2 from by ring,
      show 3 + 1 + (d + 2) = d + 6 from by ring]
  apply stepStar_trans (r4_chain (d + 6) (d + 2) e)
  rw [show e + (d + 6) = (e + 4) + (d + 2) from by ring]
  apply stepStar_trans (r5r1_chain (d + 2) 0 (e + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1 + 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d, e + 1⟩) ⟨0, 1⟩
  intro ⟨d, e⟩; exact ⟨⟨2 * d + 4, e + 3⟩, main_trans d e⟩

end Sz22_2003_unofficial_14
