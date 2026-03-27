import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #15: [1/12, 75/14, 11/2, 2/5, 196/11]

Vector representation:
```
-2 -1  0  0  0
-1  1  2 -1  0
-1  0  0  0  1
 1  0 -1  0  0
 2  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_15

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | _ => none

theorem r4r2_chain : ∀ k, ∀ b c d e, ⟨0, b, c+1, d+k, e⟩ [fm]⊢* ⟨0, b+k, c+k+1, d, e⟩ := by
  intro k; induction k with
  | zero => intro b c d e; exists 0
  | succ k ih =>
    intro b c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b+1) (c+1) d e)
    ring_nf; finish

theorem r4r3_chain : ∀ k, ∀ b e, ⟨0, b, k, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro b e; exists 0
  | succ k ih =>
    intro b e
    step fm; step fm
    apply stepStar_trans (ih b (e+1))
    ring_nf; finish

theorem r5r1_chain : ∀ k, ∀ b d e, ⟨0, b+k, 0, d, e+k⟩ [fm]⊢* ⟨0, b, 0, d+2*k, e⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (d+2) e)
    ring_nf; finish

theorem main_trans : ⟨0, 0, 0, d+1, e+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*d+6, e+3⟩ := by
  -- R5
  step fm
  -- After step fm, we have ⊢* goal. R2 twice:
  step fm; step fm
  -- Now at (0, 2, 4, d+1, e+1), goal is ⊢*
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_trans (r4r2_chain (d+1) 2 3 0 (e+1))
  rw [show 2 + (d + 1) = d + 3 from by ring]
  rw [show 3 + (d + 1) + 1 = d + 5 from by ring]
  have h3 := r4r3_chain (d+5) (d+3) (e+1)
  have h4 : ⟨0, d+3, 0, 0, e+1+(d+5)⟩ = (⟨0, 0+(d+3), 0, 0, (e+3)+(d+3)⟩ : Q) := by ring_nf
  rw [h4] at h3
  apply stepStar_trans h3
  apply stepStar_trans (r5r1_chain (d+3) 0 0 (e+3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 2⟩)
  · execute fm 16
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d+1, e+2⟩) ⟨3, 0⟩
  intro ⟨d, e⟩; exact ⟨⟨2*d+5, e+1⟩, main_trans⟩

end Sz22_2003_unofficial_15
