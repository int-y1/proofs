import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #294: [140/3, 3/55, 1/5, 121/2, 1/77, 5/11]

Vector representation:
```
 2 -1  1  1  0
 0  1 -1  0 -1
 0  0 -1  0  0
-1  0  0  0  2
 0  0  0 -1 -1
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_294

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: convert a to e.
theorem a_to_e : ∀ k a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5 repeated: cancel d and e.
theorem de_cancel : ∀ k d e, ⟨0, 0, 0, d+k, e+k⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  finish

-- (R1,R2) loop: each iteration consumes 1 from e, adds 2 to a, adds 1 to d.
theorem r1r2_loop : ∀ k a d e, ⟨a, 1, 0, d, e+k⟩ [fm]⊢* ⟨a+2*k, 1, 0, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (2*(k+1), 0, 0, k+1, 0) →⁺ (2*(3*k+2), 0, 0, 3*k+2, 0) for all k.
theorem main_trans (k : ℕ) :
    ⟨2*(k+1), 0, 0, k+1, 0⟩ [fm]⊢⁺ ⟨2*(3*k+2), 0, 0, 3*k+2, 0⟩ := by
  -- Phase 1: (2*(k+1), 0, 0, k+1, 0) →* (0, 0, 0, k+1, 4*k+4)
  have h1 : ⟨2*(k+1), 0, 0, k+1, 0⟩ [fm]⊢* ⟨0, 0, 0, k+1, 4*k+4⟩ := by
    rw [show 2*(k+1) = 0 + 2*(k+1) from by ring, show (4*k+4 : ℕ) = 0 + 2*(2*(k+1)) from by ring]
    exact a_to_e (2*(k+1)) 0 (k+1) 0
  -- Phase 2: (0, 0, 0, k+1, 4*k+4) →* (0, 0, 0, 0, 3*k+3)
  have h2 : ⟨0, 0, 0, k+1, 4*k+4⟩ [fm]⊢* ⟨0, 0, 0, 0, 3*k+3⟩ := by
    rw [show (k+1 : ℕ) = 0 + (k+1) from by ring, show (4*k+4 : ℕ) = (3*k+3) + (k+1) from by ring]
    exact de_cancel (k+1) 0 (3*k+3)
  -- Phase 3: R6, R2: (0, 0, 0, 0, 3*k+3) → (0, 0, 1, 0, 3*k+2) → (0, 1, 0, 0, 3*k+1)
  have h3 : ⟨0, 0, 0, 0, 3*k+3⟩ [fm]⊢⁺ ⟨0, 1, 0, 0, 3*k+1⟩ := by
    rw [show 3*k+3 = (3*k+1) + 1 + 1 from by ring]
    step fm; step fm; finish
  -- Phase 4: (R1,R2) loop: (0, 1, 0, 0, 3*k+1) →* (6*k+2, 1, 0, 3*k+1, 0)
  have h4 : ⟨0, 1, 0, 0, 3*k+1⟩ [fm]⊢* ⟨6*k+2, 1, 0, 3*k+1, 0⟩ := by
    have h := r1r2_loop (3*k+1) 0 0 0
    simp only [Nat.zero_add, show 2 * (3 * k + 1) = 6 * k + 2 from by ring] at h
    exact h
  -- Phase 5: R1, R3: (6*k+2, 1, 0, 3*k+1, 0) → (6*k+4, 0, 1, 3*k+2, 0) → (6*k+4, 0, 0, 3*k+2, 0)
  have h5 : ⟨6*k+2, 1, 0, 3*k+1, 0⟩ [fm]⊢⁺ ⟨2*(3*k+2), 0, 0, 3*k+2, 0⟩ := by
    have heq : (⟨6*k+4, 0, 0, 3*k+2, 0⟩ : Q) = ⟨2*(3*k+2), 0, 0, 3*k+2, 0⟩ := by
      show (6*k+4, (0 : ℕ), (0 : ℕ), 3*k+2, (0 : ℕ)) = (2*(3*k+2), (0 : ℕ), (0 : ℕ), 3*k+2, (0 : ℕ))
      congr 1; ring
    rw [← heq]
    step fm; step fm
    rw [show 6*k+2+2 = 6*k+4 from by ring, show 3*k+1+1 = 3*k+2 from by ring]
    finish
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans h1 (stepStar_trans h2 (stepPlus_stepStar h3)))
    (stepStar_stepPlus_stepPlus h4 h5)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2*1, 0, 0, 1, 0⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun k ↦ ⟨2*(k+1), 0, 0, k+1, 0⟩) 0
  intro k
  exact ⟨3*k+1, main_trans k⟩

end Sz22_2003_unofficial_294
