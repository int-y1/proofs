import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1046: [45/2, 44/35, 1/5, 7/3, 1/77, 5/7]

Vector representation:
```
-1  2  1  0  0
 2  0 -1 -1  1
 0  0 -1  0  0
 0 -1  0  1  0
 0  0  0 -1 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1046

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r2r1r1_chain : ∀ k, ∀ b c d e,
    ⟨(0 : ℕ), b, c + 1, d + k, e⟩ [fm]⊢* ⟨0, b + 4 * k, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 4) (c + 1) d (e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, k, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · finish
  · step fm
    exact ih b e

theorem r4_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih b (d + 1) e

theorem r5_chain : ∀ k, ∀ d,
    ⟨(0 : ℕ), 0, 0, d + k, k⟩ [fm]⊢* ⟨0, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    exact ih d

theorem main_trans (d : ℕ) :
    ⟨(0 : ℕ), 0, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * d + 3, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, d + 2, 0⟩ = some ⟨0, 0, 1, d + 1, 0⟩
    simp [fm]
  have h1 : ⟨(0 : ℕ), 0, 1, d + 1, 0⟩ [fm]⊢* ⟨0, 4 * (d + 1), d + 2, 0, d + 1⟩ := by
    have := r2r1r1_chain (d + 1) 0 0 0 0
    convert this using 2; ring_nf
  have h2 : ⟨(0 : ℕ), 4 * (d + 1), d + 2, 0, d + 1⟩ [fm]⊢*
      ⟨0, 4 * (d + 1), 0, 0, d + 1⟩ := by
    exact r3_chain (d + 2) (4 * (d + 1)) (d + 1)
  have h3 : ⟨(0 : ℕ), 4 * (d + 1), 0, 0, d + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * (d + 1), d + 1⟩ := by
    have := r4_chain (4 * (d + 1)) 0 0 (d + 1)
    convert this using 2; ring_nf
  have h4 : ⟨(0 : ℕ), 0, 0, 4 * (d + 1), d + 1⟩ [fm]⊢*
      ⟨0, 0, 0, 3 * d + 3, 0⟩ := by
    rw [show 4 * (d + 1) = (3 * d + 3) + (d + 1) from by ring]
    exact r5_chain (d + 1) (3 * d + 3)
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d + 2, 0⟩) 0
  intro d
  exact ⟨3 * d + 1, main_trans d⟩

end Sz22_2003_unofficial_1046
