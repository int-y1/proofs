import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1034: [405/2, 4/35, 1/45, 7/3, 5/7]

Vector representation:
```
-1  4  1  0
 2  0 -1 -1
 0 -2 -1  0
 0 -1  0  1
 0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1034

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+4, c+1, d⟩
  | ⟨a, b, c+1, d+1⟩ => some ⟨a+2, b, c, d⟩
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+1, d⟩
  | _ => none

theorem r1r1r2_chain : ∀ k, ∀ b c,
    ⟨(2 : ℕ), b, c, k⟩ [fm]⊢* ⟨2, b + 8 * k, c + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · ring_nf; finish
  · rw [show b + 8 * (k + 1) = (b + 8) + 8 * k from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 8) (c + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ b,
    ⟨(0 : ℕ), b + 2 * k, k, 0⟩ [fm]⊢* ⟨0, b, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = b + 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih b)
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ d,
    ⟨(0 : ℕ), k, 0, d⟩ [fm]⊢* ⟨0, 0, 0, d + k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

theorem main_trans (d : ℕ) :
    ⟨(0 : ℕ), 0, 0, d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * d + 4⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 0, d + 2⟩ [fm]⊢⁺ ⟨2, 0, 0, d⟩ := by
    rw [show d + 2 = d + 1 + 1 from by ring]
    step fm
    step fm
    finish
  have h2 : ⟨(2 : ℕ), 0, 0, d⟩ [fm]⊢* ⟨2, 8 * d, d, 0⟩ := by
    have := r1r1r2_chain d 0 0
    simpa using this
  have h3 : ⟨(2 : ℕ), 8 * d, d, 0⟩ [fm]⊢* ⟨0, 8 * d + 8, d + 2, 0⟩ := by
    step fm; step fm; ring_nf; finish
  have h4 : ⟨(0 : ℕ), 8 * d + 8, d + 2, 0⟩ [fm]⊢* ⟨0, 6 * d + 4, 0, 0⟩ := by
    have := r3_chain (d + 2) (6 * d + 4)
    convert this using 2; ring_nf
  have h5 : ⟨(0 : ℕ), 6 * d + 4, 0, 0⟩ [fm]⊢* ⟨0, 0, 0, 6 * d + 4⟩ := by
    have := r4_chain (6 * d + 4) 0
    convert this using 2; ring_nf
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2
      (stepStar_trans h3
        (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d + 2⟩) 0
  intro d
  exact ⟨6 * d + 2, by convert main_trans d using 2⟩
