import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #454: [28/15, 1/6, 9/7, 125/2, 6/5]

Vector representation:
```
 2 -1 -1  1
-1 -1  0  0
 0  2  0 -1
-1  0  3  0
 1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_454

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+1⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b+1, c, d⟩
  | _ => none

-- R4 chain: convert a to c (when b=0, d=0)
theorem a_to_c : ∀ k a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+3*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R3,R2,R2 drain chain: (a, 0, 0, d) ->* (a-2d, 0, 0, 0)
theorem drain : ∀ k a, ⟨a+2*k, 0, 0, k⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring]
  step fm  -- R3: (a+2k+2, 2, 0, k)
  step fm  -- R2: (a+2k+1, 1, 0, k)
  step fm  -- R2: (a+2k, 0, 0, k)
  exact h a

-- Interleaved R3,R1,R1 chain (even c)
theorem interleaved_even : ∀ k A D, ⟨A, 0, 2*(k+1), D+1⟩ [fm]⊢* ⟨A+4*(k+1), 0, 0, D+k+2⟩ := by
  intro k; induction' k with k h <;> intro A D
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h (A + 4) (D + 1))
    ring_nf; finish

-- Interleaved chain (odd c): (A, 0, 2k+1, D+1) ->* (A+4k+1, 0, 0, D+k+1)
theorem interleaved_odd : ∀ k A D, ⟨A, 0, 2*k+1, D+1⟩ [fm]⊢* ⟨A+4*k+1, 0, 0, D+k+1⟩ := by
  intro k; induction' k with k h <;> intro A D
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h (A + 4) (D + 1))
    ring_nf; finish

-- Main transition for even a (a = 2*n): (2n+1, 0, 0, 0) ⊢⁺ (6n+2, 0, 0, 0)
-- Phase 1: R4 chain -> (0, 0, 6n+3, 0)
-- Phase 2: R5, R1 -> (3, 0, 6n+1, 1)
-- Phase 3: interleaved_odd with k=3n -> (12n+4, 0, 0, 3n+1)
-- Phase 4: drain with k=3n+1 -> (6n+2, 0, 0, 0)
theorem trans_even (n : ℕ) : ⟨2*n+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨6*n+2, 0, 0, 0⟩ := by
  -- Phase 1: a_to_c
  apply stepStar_stepPlus_stepPlus
  · have h := a_to_c (2*n+1) 0 0
    simp only [Nat.zero_add, (by ring : 3 * (2 * n + 1) = 6 * n + 3)] at h; exact h
  -- Phase 2: R5, R1
  step fm; step fm
  -- Now at (3, 0, 6*n+1, 1)
  -- Phase 3: interleaved_odd
  apply stepStar_trans
  · have h := interleaved_odd (3*n) 3 0
    simp only [Nat.zero_add,
               (by ring : 2 * (3 * n) + 1 = 6 * n + 1),
               (by ring : 3 + 4 * (3 * n) + 1 = 12 * n + 4)] at h; exact h
  -- Phase 4: drain
  have h := drain (3*n+1) (6*n+2)
  rw [show 6 * n + 2 + 2 * (3 * n + 1) = 12 * n + 4 from by ring] at h; exact h

-- Main transition for odd a (a = 2*n+1): (2n+2, 0, 0, 0) ⊢⁺ (6n+5, 0, 0, 0)
-- Phase 1: R4 chain -> (0, 0, 6n+6, 0)
-- Phase 2: R5, R1 -> (3, 0, 6n+4, 1)
-- Phase 3: interleaved_even with k=3n+1 -> (12n+11, 0, 0, 3n+3)
-- Phase 4: drain with k=3n+3 -> (6n+5, 0, 0, 0)
theorem trans_odd (n : ℕ) : ⟨2*n+2, 0, 0, 0⟩ [fm]⊢⁺ ⟨6*n+5, 0, 0, 0⟩ := by
  -- Phase 1: a_to_c
  apply stepStar_stepPlus_stepPlus
  · have h := a_to_c (2*n+2) 0 0
    simp only [Nat.zero_add, (by ring : 3 * (2 * n + 2) = 6 * n + 6)] at h; exact h
  -- Phase 2: R5, R1
  step fm; step fm
  -- Now at (3, 0, 6*n+4, 1)
  -- Phase 3: interleaved_even
  apply stepStar_trans
  · have h := interleaved_even (3*n+1) 3 0
    simp only [Nat.zero_add,
               (by ring : 2 * (3 * n + 1 + 1) = 6 * n + 4),
               (by ring : 3 + 4 * (3 * n + 1 + 1) = 12 * n + 11)] at h; exact h
  -- Phase 4: drain
  have h := drain (3*n+3) (6*n+5)
  rw [show 6 * n + 5 + 2 * (3 * n + 3) = 12 * n + 11 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 0⟩) 0
  intro n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · exists 6*m+3; subst hm
    rw [show m + m + 2 = 2 * m + 2 from by ring,
        show 6 * m + 3 + 2 = 6 * m + 5 from by ring]
    exact trans_odd m
  · exists 6*m+6; subst hm
    rw [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 from by ring,
        show 6 * m + 6 + 2 = 6 * (m + 1) + 2 from by ring]
    exact trans_even (m+1)

end Sz22_2003_unofficial_454
