import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #807: [35/6, 6655/2, 4/77, 3/5, 2/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  3
 2  0  0 -1 -1
 0  1 -1  0  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_807

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+3⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem c_to_b : ∀ k b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

theorem r1r1r3_chain : ∀ k c d e, ⟨2, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨(2 : ℕ), 0, c + 2 * k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 2) (d + 1) e)
    ring_nf; finish

theorem r2r2r3_chain : ∀ k c d e, ⟨2, 0, c, d + k, e⟩ [fm]⊢* ⟨(2 : ℕ), 0, c + 2 * k, d, e + 5 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 2) d (e + 5))
    ring_nf; finish

theorem main_transition (k : ℕ) : ⟨0, 2 * k + 1, 0, 0, 4 * k + 3⟩ [fm]⊢⁺ ⟨(0 : ℕ), 4 * k + 3, 0, 0, 8 * k + 7⟩ := by
  step fm; step fm; step fm
  rw [show (4 : ℕ) * k + 1 = 3 * k + 1 + k from by ring]
  apply stepStar_trans (r1r1r3_chain k 1 0 (3 * k + 1))
  rw [show (0 : ℕ) + k = 0 + k from by ring]
  apply stepStar_trans (r2r2r3_chain k (1 + 2 * k) 0 (3 * k + 1))
  step fm; step fm
  show ⟨0, 0, 1 + 2 * k + 2 * k + 1 + 1, 0, 3 * k + 1 + 5 * k + 3 + 3⟩ [fm]⊢* ⟨(0 : ℕ), 4 * k + 3, 0, 0, 8 * k + 7⟩
  rw [show 1 + 2 * k + 2 * k + 1 + 1 = 0 + (4 * k + 3) from by ring,
      show 3 * k + 1 + 5 * k + 3 + 3 = 8 * k + 7 from by ring]
  apply stepStar_trans (c_to_b (4 * k + 3) 0 0 (8 * k + 7))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 3⟩)
  · execute fm 2
  · apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun k ↦ ⟨0, 2 * k + 1, 0, 0, 4 * k + 3⟩) 0
    intro k; exact ⟨2 * k + 1, by rw [show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring,
      show 4 * (2 * k + 1) + 3 = 8 * k + 7 from by ring]; exact main_transition k⟩

end Sz22_2003_unofficial_807
