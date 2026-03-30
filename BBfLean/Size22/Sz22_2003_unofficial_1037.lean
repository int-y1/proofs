import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1037: [45/2, 2/21, 275/3, 7/275, 3/5]

Vector representation:
```
-1  2  1  0  0
 1 -1  0 -1  0
 0 -1  2  0  1
 0  0 -2  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1037

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+2, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ b c d,
    ⟨(0 : ℕ), b + 1, c, d + k, 0⟩ [fm]⊢* ⟨0, b + k + 1, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    convert ih (b + 1) (c + 1) d using 1; ring_nf

theorem r3_chain : ∀ k, ∀ c e,
    ⟨(0 : ℕ), k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    exact ih (c + 2) (e + 1)

theorem r4_chain : ∀ k, ∀ c d,
    ⟨(0 : ℕ), 0, c + 2 * k, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih c (d + 1)

theorem main_trans (c d : ℕ) :
    ⟨(0 : ℕ), 0, c + 1, d + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, c + d + 2, d + 3, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, c + 1, d + 2, 0⟩ = some ⟨0, 1, c, d + 2, 0⟩
    unfold fm; simp
  have h1 : ⟨(0 : ℕ), 1, c, d + 2, 0⟩ [fm]⊢*
      ⟨0, d + 3, c + d + 2, 0, 0⟩ := by
    have := r2r1_chain (d + 2) 0 c 0
    convert this using 1; ring_nf
  have h2 : ⟨(0 : ℕ), d + 3, c + d + 2, 0, 0⟩ [fm]⊢*
      ⟨0, 0, c + d + 2 + 2 * (d + 3), 0, d + 3⟩ := by
    have := r3_chain (d + 3) (c + d + 2) 0
    convert this using 1; ring_nf
  have h3 : ⟨(0 : ℕ), 0, c + d + 2 + 2 * (d + 3), 0, d + 3⟩ [fm]⊢*
      ⟨0, 0, c + d + 2, d + 3, 0⟩ := by
    have := r4_chain (d + 3) (c + d + 2) 0
    convert this using 1; ring_nf
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 2, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, d⟩ ↦ ⟨0, 0, c + 1, d + 2, 0⟩) ⟨0, 0⟩
  intro ⟨c, d⟩
  exact ⟨⟨c + d + 1, d + 1⟩, main_trans c d⟩

end Sz22_2003_unofficial_1037
