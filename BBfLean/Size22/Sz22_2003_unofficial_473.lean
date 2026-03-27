import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #473: [28/15, 21/22, 325/2, 11/7, 3/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  1 -1  0
-1  0  2  0  0  1
 0  0  0 -1  1  0
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_473

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- Phase: R4 chain d → e
theorem d_to_e : ∀ k, ∀ c e f, ⟨0, 0, c, k, e, f⟩ [fm]⊢* ⟨0, 0, c, 0, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · simp; exists 0
  have h1 : ⟨0, 0, c, k + 1, e, f⟩ [fm]⊢ ⟨0, 0, c, k, e + 1, f⟩ := by
    show fm ⟨0, 0, c, k + 1, e, f⟩ = some ⟨0, 0, c, k, e + 1, f⟩; simp [fm]
  have h2 := ih c (e + 1) f
  have h3 := stepStar_trans (step_stepStar h1) h2
  rw [show e + 1 + k = e + (k + 1) from by ring] at h3
  exact h3

-- Phase: R3 chain a → c, f
theorem a_to_cf : ∀ k, ∀ c d f, ⟨k, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · simp; exists 0
  have h1 : ⟨k + 1, 0, c, d, 0, f⟩ [fm]⊢ ⟨k, 0, c + 2, d, 0, f + 1⟩ := by
    show fm ⟨k + 1, 0, c, d, 0, f⟩ = some ⟨k, 0, c + 2, d, 0, f + 1⟩; simp [fm]
  have h2 := ih (c + 2) d (f + 1)
  have h3 := stepStar_trans (step_stepStar h1) h2
  rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring,
      show f + 1 + k = f + (k + 1) from by ring] at h3
  exact h3

-- Phase: R1/R2 interleaved chain
-- (A, 1, C+e+1, D, e, f) ⊢* (A+e+2, 0, C, D+2*e+1, 0, f)
theorem r1r2_chain : ∀ e, ∀ A C D f,
    ⟨A, 1, C + e + 1, D, e, f⟩ [fm]⊢* ⟨A + e + 2, 0, C, D + 2 * e + 1, 0, f⟩ := by
  intro e; induction' e with e ih <;> intro A C D f
  · simp
    have h1 : ⟨A, 1, C + 1, D, 0, f⟩ [fm]⊢ ⟨A + 2, 0, C, D + 1, 0, f⟩ := by
      show fm ⟨A, 0 + 1, C + 1, D, 0, f⟩ = some ⟨A + 2, 0, C, D + 1, 0, f⟩; simp [fm]
    exact step_stepStar h1
  rw [show C + (e + 1) + 1 = (C + e + 1) + 1 from by ring]
  -- R1: (A, 1, (C+e+1)+1, D, e+1, f) -> (A+2, 0, C+e+1, D+1, e+1, f)
  have h1 : ⟨A, 1, (C + e + 1) + 1, D, e + 1, f⟩ [fm]⊢ ⟨A + 2, 0, C + e + 1, D + 1, e + 1, f⟩ := by
    show fm ⟨A, 0 + 1, (C + e + 1) + 1, D, e + 1, f⟩ = some ⟨A + 2, 0, C + e + 1, D + 1, e + 1, f⟩
    simp [fm]
  -- R2: (A+2, 0, C+e+1, D+1, e+1, f) -> (A+1, 1, C+e+1, D+2, e, f)
  have h2 : ⟨A + 2, 0, C + e + 1, D + 1, e + 1, f⟩ [fm]⊢ ⟨A + 1, 1, C + e + 1, D + 2, e, f⟩ := by
    show fm ⟨(A + 1) + 1, 0, C + e + 1, D + 1, e + 1, f⟩ = some ⟨A + 1, 0 + 1, C + e + 1, (D + 1) + 1, e, f⟩
    simp [fm]
  -- IH: (A+1, 1, C+e+1, D+2, e, f) ⊢* (A+1+e+2, 0, C, D+2+2*e+1, 0, f)
  have h3 := ih (A + 1) C (D + 2) f
  have h4 := stepStar_trans (step_stepStar h1) (stepStar_trans (step_stepStar h2) h3)
  rw [show A + 1 + e + 2 = A + (e + 1) + 2 from by ring,
      show D + 2 + 2 * e + 1 = D + 2 * (e + 1) + 1 from by ring] at h4
  exact h4

-- Main transition: canonical state (0, 0, g+e+2, 0, e, e+1) ⊢⁺ (0, 0, (g+2)+(2*e+1)+2, 0, 2*e+1, 2*e+2)
theorem main_trans (g e : ℕ) :
    ⟨0, 0, g + e + 2, 0, e, e + 1⟩ [fm]⊢⁺ ⟨0, 0, (g + 2) + (2 * e + 1) + 2, 0, 2 * e + 1, 2 * e + 2⟩ := by
  -- Phase 1: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, g + e + 2, 0, e, e⟩)
  · show fm ⟨0, 0, g + e + 2, 0, e, e + 1⟩ = some ⟨0, 0 + 1, g + e + 2, 0, e, e⟩; simp [fm]
  -- Phase 2: R1/R2 chain: (0, 1, g+e+2, 0, e, e) ⊢* (e+2, 0, g+1, 2*e+1, 0, e)
  -- r1r2_chain with A=0, C=g+1, D=0, f=e: need C+e+1 = g+1+e+1 = g+e+2
  apply stepStar_trans (c₂ := ⟨e + 2, 0, g + 1, 2 * e + 1, 0, e⟩)
  · have h := r1r2_chain e 0 (g + 1) 0 e
    rw [show g + 1 + e + 1 = g + e + 2 from by ring,
        show 0 + e + 2 = e + 2 from by ring,
        show 0 + 2 * e + 1 = 2 * e + 1 from by ring] at h
    exact h
  -- Phase 3: R3 chain: (e+2, 0, g+1, 2*e+1, 0, e) ⊢* (0, 0, g+2e+5, 2*e+1, 0, 2*e+2)
  apply stepStar_trans (c₂ := ⟨0, 0, (g + 2) + (2 * e + 1) + 2, 2 * e + 1, 0, 2 * e + 2⟩)
  · have h := a_to_cf (e + 2) (g + 1) (2 * e + 1) e
    rw [show g + 1 + 2 * (e + 2) = (g + 2) + (2 * e + 1) + 2 from by ring,
        show e + (e + 2) = 2 * e + 2 from by ring] at h
    exact h
  -- Phase 4: R4 chain: d → e
  have h := d_to_e (2 * e + 1) ((g + 2) + (2 * e + 1) + 2) 0 (2 * e + 2)
  rw [show 0 + (2 * e + 1) = 2 * e + 1 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨g, e⟩ ↦ ⟨0, 0, g + e + 2, 0, e, e + 1⟩) ⟨0, 0⟩
  intro ⟨g, e⟩; exact ⟨⟨g + 2, 2 * e + 1⟩, main_trans g e⟩
