import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #130: [9/10, 55/21, 4/3, 7/11, 33/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  0
 0  0  0  1 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_130

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Phase 4: R4 repeated: e → d
theorem e_to_d : ∀ k, ∀ a d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show d + (k + 1) = (d + 1) + k from by ring]
  step fm
  exact ih a (d + 1)

-- Phase 3: R3 repeated: b → a (when c=0, d=0)
theorem b_to_a : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  step fm
  apply stepStar_trans (ih _ e)
  ring_nf; finish

-- Phase 2: One (R2, R1) pair
-- From (A+1, B+1, 0, D+1, E+1):
--   R2 (b≥1, d≥1): (A+1, B, 1, D, E+2)
--   R1 (a≥1, c≥1): (A, B+2, 0, D, E+2)
theorem r2r1_one_step (A B D E : ℕ) :
    ⟨A + 1, B + 1, 0, D + 1, E + 1⟩ [fm]⊢* ⟨A, B + 2, 0, D, E + 2⟩ := by
  step fm
  step fm
  finish

-- Phase 2: k pairs of (R2, R1)
-- Induction: (A+k, B+1, 0, D+k, E+1) →* (A, B+k+1, 0, D, E+k+1)
theorem r2r1_pairs : ∀ k, ∀ A B D E, ⟨A + k, B + 1, 0, D + k, E + 1⟩ [fm]⊢* ⟨A, B + k + 1, 0, D, E + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A B D E
  · exists 0
  -- State: (A+(k+1), B+1, 0, D+(k+1), E+1)
  -- = ((A+k)+1, B+1, 0, (D+k)+1, E+1)
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show D + (k + 1) = (D + k) + 1 from by ring]
  -- Apply one (R2, R1) pair
  apply stepStar_trans (r2r1_one_step (A + k) B (D + k) E)
  -- Now at: (A+k, B+2, 0, D+k, E+2)
  -- = (A+k, (B+1)+1, 0, D+k, (E+1)+1)
  rw [show B + 2 = (B + 1) + 1 from by ring,
      show E + 2 = (E + 1) + 1 from by ring]
  apply stepStar_trans (ih A (B + 1) D (E + 1))
  ring_nf; finish

-- Main transition: (a+n+1, 0, 0, n, 0) →⁺ (a+2*n+2, 0, 0, n+1, 0)
theorem main_trans (a n : ℕ) : ⟨a + n + 1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨a + 2 * n + 2, 0, 0, n + 1, 0⟩ := by
  -- Phase 1: R5: (a+n+1, 0, 0, n, 0) -> (a+n, 1, 0, n, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨a + n, 1, 0, n, 1⟩)
  · show fm ⟨(a + n) + 1, 0, 0, n, 0⟩ = some ⟨a + n, 1, 0, n, 1⟩
    simp [fm]
  -- Phase 2: n (R2,R1) pairs: (a+n, 1, 0, n, 1) -> (a, n+1, 0, 0, n+1)
  -- Use r2r1_pairs with A=a, B=0, D=0, E=0, k=n
  -- Need: (a+n, 0+1, 0, 0+n, 0+1) →* (a, 0+n+1, 0, 0, 0+n+1)
  apply stepStar_trans (c₂ := ⟨a, n + 1, 0, 0, n + 1⟩)
  · have h := r2r1_pairs n a 0 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 3: (n+1) R3 steps: (a, n+1, 0, 0, n+1) -> (a+2*(n+1), 0, 0, 0, n+1)
  apply stepStar_trans (c₂ := ⟨a + 2 * (n + 1), 0, 0, 0, n + 1⟩)
  · exact b_to_a (n + 1) a (n + 1)
  -- Phase 4: (n+1) R4 steps
  have h := e_to_d (n + 1) (a + 2 * (n + 1)) 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 2, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a + n + 1, 0, 0, n, 0⟩) ⟨1, 2⟩
  intro ⟨a, n⟩
  refine ⟨⟨a + n, n + 1⟩, ?_⟩
  show ⟨a + n + 1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨a + n + (n + 1) + 1, 0, 0, n + 1, 0⟩
  have h := main_trans a n
  convert h using 2
  ring_nf

end Sz21_140_unofficial_130
