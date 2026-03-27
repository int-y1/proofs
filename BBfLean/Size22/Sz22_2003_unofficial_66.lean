import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #66: [1/18, 1925/2, 2/91, 39/5, 2/33]

Vector representation:
```
-1 -2  0  0  0  0
-1  0  2  1  1  0
 1  0  0 -1  0 -1
 0  1 -1  0  0  1
 1 -1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_66

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- Phase 1: R4 chain — convert c to b and f
theorem c_to_bf : ∀ k, ∀ b c e f, ⟨0, b, c+k, 0, e, f⟩ [fm]⊢* ⟨0, b+k, c, 0, e, f+k⟩ := by
  intro k; induction' k with k ih <;> intro b c e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Phase 2: R5+R1 drain — each round removes 3 from b and 1 from e
theorem r5r1_drain : ∀ k, ∀ b e f, ⟨0, b+3*k, 0, 0, e+k, f⟩ [fm]⊢* ⟨0, b, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring,
      show (b + 3 * k) + 3 = (b + 3 * k + 2) + 1 from by ring]
  step fm  -- R5: (1, b+3k+1, 0, 0, e+k, f)
  rw [show b + 3 * k + 2 = (b + 3 * k) + 2 from by ring]
  step fm  -- R1: (0, b+3k, 0, 0, e+k, f)
  exact ih _ _ _

-- Phase 3: R3+R2 chain — interleaves R3 and R2
theorem r3r2_chain : ∀ k, ∀ c e f, ⟨0, 1, c, 1, e, f+k⟩ [fm]⊢* ⟨0, 1, c+2*k, 1, e+k, f⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  rw [show f + (k + 1) = (f + k) + 1 from by ring]
  step fm  -- R3: (1, 1, c, 0, e, f+k)
  step fm  -- R2: (0, 1, c+2, 1, e+1, f+k)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: C(m) = (0, 0, 3*(m+1)-1, 0, 2*(m+1), 0) ⊢⁺ C(2*m+1)
-- i.e., (0, 0, 3*m+2, 0, 2*m+2, 0) ⊢⁺ (0, 0, 6*m+5, 0, 4*m+4, 0)
theorem main_trans (m : ℕ) : ⟨0, 0, 3*m+2, 0, 2*m+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 6*m+5, 0, 4*m+4, 0⟩ := by
  -- Phase 1: R4 chain (3*m+2 steps)
  apply stepStar_stepPlus_stepPlus
  · have h := c_to_bf (3*m+2) 0 0 (2*m+2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Now at (0, 3*m+2, 0, 0, 2*m+2, 3*m+2)
  -- Phase 2: R5+R1 drain (m rounds)
  -- b = 3*m+2 = 2 + 3*m, e = 2*m+2 = (m+2) + m
  apply stepStar_stepPlus_stepPlus
  · have h := r5r1_drain m 2 (m+2) (3*m+2)
    simp only [(by ring : 2 + 3 * m = 3 * m + 2),
               (by ring : m + 2 + m = 2 * m + 2)] at h
    exact h
  -- Now at (0, 2, 0, 0, m+2, 3*m+2)
  -- Phase 2b: R5 then R2
  rw [show m + 2 = (m + 1) + 1 from by ring]
  step fm  -- R5: (1, 1, 0, 0, m+1, 3*m+2)
  step fm  -- R2: (0, 1, 2, 1, m+2, 3*m+2)
  -- Phase 3: R3+R2 chain (3*m+2 rounds)
  apply stepStar_trans
  · have h := r3r2_chain (3*m+2) 2 (m+2) 0
    simp only [(by ring : 0 + (3 * m + 2) = 3 * m + 2),
               (by ring : 2 + 2 * (3 * m + 2) = 6 * m + 6),
               (by ring : m + 2 + (3 * m + 2) = 4 * m + 4)] at h
    exact h
  -- Now at (0, 1, 6*m+6, 1, 4*m+4, 0)
  -- Phase 4: R4, R3, R1
  rw [show 6 * m + 6 = (6 * m + 5) + 1 from by ring]
  step fm  -- R4: (0, 2, 6*m+5, 1, 4*m+4, 1)
  step fm  -- R3: (1, 2, 6*m+5, 0, 4*m+4, 0)
  step fm  -- R1: (0, 0, 6*m+5, 0, 4*m+4, 0)
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 2, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨0, 0, 3*m+2, 0, 2*m+2, 0⟩) 0
  intro m; exists 2*m+1
  show ⟨0, 0, 3 * m + 2, 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * (2 * m + 1) + 2, 0, 2 * (2 * m + 1) + 2, 0⟩
  simp only [(by ring : 3 * (2 * m + 1) + 2 = 6 * m + 5),
             (by ring : 2 * (2 * m + 1) + 2 = 4 * m + 4)]
  exact main_trans m

end Sz22_2003_unofficial_66
