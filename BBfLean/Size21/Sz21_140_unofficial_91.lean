import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #91: [5/6, 77/2, 52/35, 3/13, 15/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  1  1  0
 2  0 -1 -1  0  1
 0  1  0  0  0 -1
 0  1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_91

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: f → b
theorem f_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d, e, k⟩ [fm]⊢* ⟨0, b+k, 0, d, e, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  show ∃ n, stepNat fm n ⟨0, b, 0, d, e, k + 1⟩ = some ⟨0, b + (k + 1), 0, d, e, 0⟩
  have h1 : ⟨0, b, 0, d, e, k + 1⟩ [fm]⊢ ⟨0, b + 1, 0, d, e, k⟩ := by
    show fm ⟨0, b, 0, d, e, k + 1⟩ = some ⟨0, b + 1, 0, d, e, k⟩; simp [fm]
  have h2 := ih (b + 1) d e
  have h3 := stepStar_trans (step_stepStar h1) h2
  rw [show b + 1 + k = b + (k + 1) from by ring] at h3
  exact h3

-- R3R1R1 chain
theorem r3r1r1_chain : ∀ k, ∀ B C D E F, ⟨0, 2*k+B, C+1, D+k, E, F⟩ [fm]⊢* ⟨0, B, C+k+1, D, E, F+k⟩ := by
  intro k; induction' k with k ih <;> intro B C D E F
  · simp; exists 0
  rw [show 2 * (k + 1) + B = (2 * k + B + 1) + 1 from by ring,
      show D + (k + 1) = D + k + 1 from by ring]
  have h1 : ⟨0, (2*k+B+1)+1, C+1, (D+k)+1, E, F⟩ [fm]⊢ ⟨2, (2*k+B+1)+1, C, D+k, E, F+1⟩ := by
    show fm ⟨0, (2*k+B+1)+1, C+1, (D+k)+1, E, F⟩ = some ⟨0+2, (2*k+B+1)+1, C, D+k, E, F+1⟩
    simp [fm]
  have h2 : ⟨2, (2*k+B+1)+1, C, D+k, E, F+1⟩ [fm]⊢ ⟨1, 2*k+B+1, C+1, D+k, E, F+1⟩ := by
    show fm ⟨1+1, (2*k+B+1)+1, C, D+k, E, F+1⟩ = some ⟨1, 2*k+B+1, C+1, D+k, E, F+1⟩
    simp [fm]
  have h3 : ⟨1, (2*k+B)+1, C+1, D+k, E, F+1⟩ [fm]⊢ ⟨0, 2*k+B, C+2, D+k, E, F+1⟩ := by
    show fm ⟨0+1, (2*k+B)+1, C+1, D+k, E, F+1⟩ = some ⟨0, 2*k+B, C+2, D+k, E, F+1⟩
    simp [fm]
  rw [show 2 * k + B + 1 = (2 * k + B) + 1 from by ring] at h2
  have h4 := ih B (C+1) D E (F+1)
  rw [show C + 2 = (C + 1) + 1 from by ring] at h3
  have h5 : ⟨0, (2*k+B+1)+1, C+1, (D+k)+1, E, F⟩ [fm]⊢* ⟨0, B, C+1+k+1, D, E, F+1+k⟩ :=
    stepStar_trans (step_stepStar h1) (stepStar_trans (step_stepStar h2) (stepStar_trans (step_stepStar h3) h4))
  rw [show C + 1 + k + 1 = C + (k + 1) + 1 from by ring,
      show F + 1 + k = F + (k + 1) from by ring] at h5
  exact h5

-- R3R2R2 chain
theorem r3r2r2_chain : ∀ k, ∀ C D E F, ⟨0, 0, C+k, D+1, E, F⟩ [fm]⊢* ⟨0, 0, C, D+k+1, E+2*k, F+k⟩ := by
  intro k; induction' k with k ih <;> intro C D E F
  · simp; exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring]
  have h1 : ⟨0, 0, (C+k)+1, D+1, E, F⟩ [fm]⊢ ⟨2, 0, C+k, D, E, F+1⟩ := by
    show fm ⟨0, 0, (C+k)+1, D+1, E, F⟩ = some ⟨0+2, 0, C+k, D, E, F+1⟩; simp [fm]
  have h2 : ⟨2, 0, C+k, D, E, F+1⟩ [fm]⊢ ⟨1, 0, C+k, D+1, E+1, F+1⟩ := by
    show fm ⟨1+1, 0, C+k, D, E, F+1⟩ = some ⟨1, 0, C+k, D+1, E+1, F+1⟩; simp [fm]
  have h3 : ⟨1, 0, C+k, D+1, E+1, F+1⟩ [fm]⊢ ⟨0, 0, C+k, D+2, E+2, F+1⟩ := by
    show fm ⟨0+1, 0, C+k, D+1, E+1, F+1⟩ = some ⟨0, 0, C+k, D+2, E+2, F+1⟩; simp [fm]
  have h4 := ih C (D+1) (E+2) (F+1)
  rw [show D + 2 = (D + 1) + 1 from by ring] at h3
  have h5 : ⟨0, 0, (C+k)+1, D+1, E, F⟩ [fm]⊢* ⟨0, 0, C, D+1+k+1, E+2+2*k, F+1+k⟩ :=
    stepStar_trans (step_stepStar h1) (stepStar_trans (step_stepStar h2) (stepStar_trans (step_stepStar h3) h4))
  rw [show D + 1 + k + 1 = D + (k + 1) + 1 from by ring,
      show E + 2 + 2 * k = E + 2 * (k + 1) from by ring,
      show F + 1 + k = F + (k + 1) from by ring] at h5
  exact h5

-- Main transition: C(n) →⁺ C(n+1)
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n+1, n*n+n+1, 2*n⟩ [fm]⊢⁺ ⟨0, 0, 0, n+2, (n+1)*(n+1)+(n+1)+1, 2*(n+1)⟩ := by
  -- Phase A: f_to_b
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*n, 0, n+1, n*n+n+1, 0⟩)
  · have h := f_to_b (2*n) 0 (n+1) (n*n+n+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase B: R5
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*n+1, 1, n+1, n*n+n, 0⟩)
  · show fm ⟨0, 2*n, 0, n+1, (n*n+n)+1, 0⟩ = some ⟨0, 2*n+1, 1, n+1, n*n+n, 0⟩
    rw [show n * n + n + 1 = n * n + n + 1 from rfl]; simp [fm]
  -- Phase C: r3r1r1_chain
  apply stepStar_trans (c₂ := ⟨0, 1, n+1, 1, n*n+n, n⟩)
  · have h := r3r1r1_chain n 1 0 1 (n*n+n) 0
    rw [show 2 * n + 1 = 2 * n + 1 from rfl,
        show 0 + 1 = 1 from rfl,
        show 1 + n = n + 1 from by ring,
        show 0 + n + 1 = n + 1 from by ring,
        show 0 + n = n from by ring] at h
    exact h
  -- Phase D: R3
  apply stepStar_trans (c₂ := ⟨2, 1, n, 0, n*n+n, n+1⟩)
  · apply step_stepStar
    show fm ⟨0, 1, n+1, 1, n*n+n, n⟩ = some ⟨0+2, 1, n, 0, n*n+n, n+1⟩
    rw [show n + 1 = n + 1 from rfl]; simp [fm]
  -- Phase E: R1
  apply stepStar_trans (c₂ := ⟨1, 0, n+1, 0, n*n+n, n+1⟩)
  · apply step_stepStar
    show fm ⟨1+1, 0+1, n, 0, n*n+n, n+1⟩ = some ⟨1, 0, n+1, 0, n*n+n, n+1⟩
    simp [fm]
  -- Phase F: R2
  apply stepStar_trans (c₂ := ⟨0, 0, n+1, 1, n*n+n+1, n+1⟩)
  · apply step_stepStar
    show fm ⟨0+1, 0, n+1, 0, n*n+n, n+1⟩ = some ⟨0, 0, n+1, 0+1, (n*n+n)+1, n+1⟩
    simp [fm]
  -- Phase G: r3r2r2_chain
  have h := r3r2r2_chain (n+1) 0 0 (n*n+n+1) (n+1)
  simp only [Nat.zero_add] at h
  rw [show n + 1 + 1 = n + 2 from by ring,
      show n * n + n + 1 + 2 * (n + 1) = (n + 1) * (n + 1) + (n + 1) + 1 from by ring,
      show n + 1 + (n + 1) = 2 * (n + 1) from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, 0, n+1, n*n+n+1, 2*n⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
