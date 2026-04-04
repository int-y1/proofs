import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1793: [9/10, 49/2, 22/21, 5/121, 10/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  2  0
 1 -1  0 -1  1
 0  0  1  0 -2
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1793

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 chain: (0, 0, c, d, e + 2*k) →* (0, 0, c + k, d, e)
theorem r4_chain : ∀ k c d e, ⟨(0 : ℕ), 0, c, d, e + 2 * k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    apply stepStar_trans (ih c d (e + 2))
    step fm
    ring_nf; finish

-- R1+R3 interleave: (1, 0, k + c, k + d, e) →* (1, k, c, d, e + k)
theorem r1r3_chain : ∀ k, ∀ c d e, ⟨(1 : ℕ), 0, k + c, k + d, e⟩ [fm]⊢* ⟨1, k, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · ring_nf; finish
  · rw [show k + 1 + c = k + (c + 1) from by ring,
        show k + 1 + d = k + (d + 1) from by ring]
    apply stepStar_trans (ih (c + 1) (d + 1) e)
    step fm
    step fm
    ring_nf; finish

-- R3+R2 drain: (0, k + b, 0, d + 1, e) →* (0, b, 0, d + k + 1, e + k)
theorem r3r2_chain : ∀ k, ∀ b d e, ⟨(0 : ℕ), k + b, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show k + 1 + b = k + (b + 1) from by ring]
    apply stepStar_trans (ih (b + 1) d e)
    step fm
    step fm
    ring_nf; finish

-- Main transition: (0, 0, 0, n+2, 2*n) ⊢⁺ (0, 0, 0, n+3, 2*(n+1))
theorem main_trans (n : ℕ) : ⟨(0 : ℕ), 0, 0, n + 2, 2 * n⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 3, 2 * (n + 1)⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 0, n + 2, 2 * n⟩ [fm]⊢* ⟨0, 0, n, n + 2, 0⟩ := by
    rw [show (2 : ℕ) * n = 0 + 2 * n from by ring]
    have := r4_chain n 0 (n + 2) 0
    rw [show (0 : ℕ) + n = n from by ring] at this
    exact this
  have h2 : ⟨(0 : ℕ), 0, n, n + 2, 0⟩ [fm]⊢ ⟨1, 0, n + 1, n + 1, 0⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]; simp [fm]
  have h3 : ⟨(1 : ℕ), 0, n + 1, n + 1, 0⟩ [fm]⊢* ⟨1, n + 1, 0, 0, n + 1⟩ := by
    have := r1r3_chain (n + 1) 0 0 0
    simp at this; exact this
  have h4 : ⟨(1 : ℕ), n + 1, 0, 0, n + 1⟩ [fm]⊢ ⟨0, n + 1, 0, 2, n + 1⟩ := by
    simp [fm]
  have h5 : ⟨(0 : ℕ), n + 1, 0, 2, n + 1⟩ [fm]⊢* ⟨0, 0, 0, n + 3, 2 * (n + 1)⟩ := by
    have := r3r2_chain (n + 1) 0 1 (n + 1)
    simp at this
    rw [show 1 + (n + 1) + 1 = n + 3 from by ring,
        show n + 1 + (n + 1) = 2 * (n + 1) from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans (step_stepStar h4) h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 2 * n⟩) 0
  intro n; exists n + 1; exact main_trans n
