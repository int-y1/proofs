import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1036: [45/2, 2/21, 11/3, 343/55, 3/77]

Vector representation:
```
-1  2  1  0  0
 1 -1  0 -1  0
 0 -1  0  0  1
 0  0 -1  3 -1
 0  1  0 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1036

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r1r2_chain : ∀ k, ∀ b c d,
    ⟨(1 : ℕ), b, c, d + k, 0⟩ [fm]⊢* ⟨1, b + k, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) (c + 1) d)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ c e,
    ⟨(0 : ℕ), k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih c (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ d e,
    ⟨(0 : ℕ), 0, k, d, e + k⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring]
    step fm
    apply stepStar_trans (ih (d + 3) e)
    ring_nf; finish

theorem main_trans (D : ℕ) :
    ⟨(1 : ℕ), 0, 0, D + 1, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 3 * D + 4, 0⟩ := by
  have h1 : ⟨(1 : ℕ), 0, 0, D + 1, 0⟩ [fm]⊢*
      ⟨1, D + 1, D + 1, 0, 0⟩ := by
    have := r1r2_chain (D + 1) 0 0 0
    convert this using 2; ring_nf
  have h2 : ⟨(1 : ℕ), D + 1, D + 1, 0, 0⟩ [fm]⊢⁺
      ⟨0, D + 3, D + 2, 0, 0⟩ := by
    step fm; finish
  have h3 : ⟨(0 : ℕ), D + 3, D + 2, 0, 0⟩ [fm]⊢*
      ⟨0, 0, D + 2, 0, D + 3⟩ := by
    have := r3_chain (D + 3) (D + 2) 0
    convert this using 2; ring_nf
  have h4 : ⟨(0 : ℕ), 0, D + 2, 0, D + 3⟩ [fm]⊢*
      ⟨0, 0, 0, 3 * D + 6, 1⟩ := by
    have := r4_chain (D + 2) 0 1
    convert this using 2; ring_nf
  have h5 : ⟨(0 : ℕ), 0, 0, 3 * D + 6, 1⟩ [fm]⊢*
      ⟨1, 0, 0, 3 * D + 4, 0⟩ := by
    step fm; step fm; finish
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun D ↦ ⟨1, 0, 0, D + 1, 0⟩) 0
  intro D
  exact ⟨3 * D + 3, main_trans D⟩

end Sz22_2003_unofficial_1036
