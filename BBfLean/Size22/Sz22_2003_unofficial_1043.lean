import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1043: [45/2, 4/35, 11/5, 7/33, 5/3, 1/11]

Vector representation:
```
-1  2  1  0  0
 2  0 -1 -1  0
 0  0 -1  0  1
 0 -1  0  1 -1
 0 -1  1  0  0
 0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1043

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k b e,
    ⟨(0 : ℕ), b, k, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · step fm
    rw [show e + (k + 1) = (e + 1) + k from by ring]
    exact ih b (e + 1)

theorem r4_chain : ∀ k b d,
    ⟨(0 : ℕ), b + k, 0, d, k⟩ [fm]⊢* ⟨0, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih b (d + 1)

theorem r2r1r1_chain : ∀ d X k,
    ⟨(0 : ℕ), X, k + 1, d, 0⟩ [fm]⊢* ⟨0, X + 4 * d, k + d + 1, 0, 0⟩ := by
  intro d; induction' d with d ih <;> intro X k
  · ring_nf; finish
  · rw [show k + (d + 1) + 1 = (k + 1) + d + 1 from by ring,
        show X + 4 * (d + 1) = (X + 4) + 4 * d from by ring]
    step fm; step fm; step fm
    exact ih (X + 4) (k + 1)

theorem main_trans (b c : ℕ) :
    ⟨(0 : ℕ), b + c + 3, c + 2, 0, 0⟩ [fm]⊢⁺ ⟨0, b + 4 * c + 8, c + 3, 0, 0⟩ := by
  have phase1 : ⟨(0 : ℕ), b + c + 3, c + 2, 0, 0⟩ [fm]⊢* ⟨0, b + c + 3, 0, 0, c + 2⟩ := by
    have h := r3_chain (c + 2) (b + c + 3) 0
    convert h using 1; ext; all_goals ring_nf
  have phase2 : ⟨(0 : ℕ), b + c + 3, 0, 0, c + 2⟩ [fm]⊢* ⟨0, b + 1, 0, c + 2, 0⟩ := by
    have h := r4_chain (c + 2) (b + 1) 0
    rw [show b + 1 + (c + 2) = b + c + 3 from by ring,
        show 0 + (c + 2) = c + 2 from by ring] at h
    exact h
  have phase3 : ⟨(0 : ℕ), b + 1, 0, c + 2, 0⟩ [fm]⊢ ⟨0, b, 1, c + 2, 0⟩ := by
    show fm ⟨0, b + 1, 0, c + 2, 0⟩ = some ⟨0, b, 1, c + 2, 0⟩
    simp [fm]
  have phase4 : ⟨(0 : ℕ), b, 1, c + 2, 0⟩ [fm]⊢* ⟨0, b + 4 * c + 8, c + 3, 0, 0⟩ := by
    have h := r2r1r1_chain (c + 2) b 0
    convert h using 1; ext; all_goals ring_nf
  exact stepStar_stepPlus_stepPlus phase1
    (stepStar_stepPlus_stepPlus phase2
      (step_stepStar_stepPlus phase3 phase4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 4, 2, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨b, c⟩ ↦ ⟨0, b + c + 3, c + 2, 0, 0⟩) ⟨1, 0⟩
  intro ⟨b, c⟩
  refine ⟨⟨b + 3 * c + 4, c + 1⟩, ?_⟩
  have h := main_trans b c
  convert h using 1; ext; all_goals ring_nf

end Sz22_2003_unofficial_1043
