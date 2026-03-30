import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1044: [45/2, 4/35, 11/5, 7/33, 5/3, 1/7]

Vector representation:
```
-1  2  1  0  0
 2  0 -1 -1  0
 0  0 -1  0  1
 0 -1  0  1 -1
 0 -1  1  0  0
 0  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1044

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

theorem r2r1r1_chain : ∀ k, ∀ b c d,
    ⟨(0 : ℕ), b, c + 1, d + k, 0⟩ [fm]⊢* ⟨0, b + 4 * k, c + k + 1, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    have := ih (b + 4) (c + 1) d
    convert this using 1; ext; all_goals ring_nf

theorem r3_chain : ∀ k, ∀ b e,
    ⟨(0 : ℕ), b, k, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · step fm
    have := ih b (e + 1)
    convert this using 1; ext; all_goals ring_nf

theorem r4_chain : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b + k, 0, d, k⟩ [fm]⊢* ⟨0, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih b (d + 1)

theorem main_trans (b d : ℕ) :
    ⟨(0 : ℕ), b + 1, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨0, b + 3 * d + 2, 0, d + 2, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, b + 1, 0, d + 1, 0⟩ = some ⟨0, b, 1, d + 1, 0⟩
    unfold fm; simp
  have h1 : ⟨(0 : ℕ), b, 1, d + 1, 0⟩ [fm]⊢* ⟨0, b + 4 * (d + 1), d + 2, 0, 0⟩ := by
    have := r2r1r1_chain (d + 1) b 0 0
    convert this using 1; ext; all_goals ring_nf
  have h2 : ⟨(0 : ℕ), b + 4 * (d + 1), d + 2, 0, 0⟩ [fm]⊢*
      ⟨0, b + 4 * (d + 1), 0, 0, d + 2⟩ := by
    have := r3_chain (d + 2) (b + 4 * (d + 1)) 0
    convert this using 1; ext; all_goals ring_nf
  have h3 : ⟨(0 : ℕ), b + 4 * (d + 1), 0, 0, d + 2⟩ [fm]⊢*
      ⟨0, b + 3 * d + 2, 0, d + 2, 0⟩ := by
    rw [show b + 4 * (d + 1) = (b + 3 * d + 2) + (d + 2) from by ring]
    have := r4_chain (d + 2) (b + 3 * d + 2) 0
    convert this using 1; ext; all_goals ring_nf
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨b, d⟩ ↦ ⟨0, b + 1, 0, d + 1, 0⟩) ⟨0, 0⟩
  intro ⟨b, d⟩
  exact ⟨⟨b + 3 * d + 1, d + 1⟩, main_trans b d⟩

end Sz22_2003_unofficial_1044
