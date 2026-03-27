import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #570: [35/6, 1/385, 4/5, 77/2, 45/7]

Vector representation:
```
-1 -1  1  1  0
 0  0 -1 -1 -1
 2  0 -1  0  0
-1  0  0  1  1
 0  2  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_570

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | _ => none

-- R4 chain: (A+k, 0, 0, d, e) →* (A, 0, 0, d+k, e+k)
theorem r4_chain : ∀ k, ∀ A d e, ⟨A+k, 0, 0, d, e⟩ [fm]⊢* ⟨A, 0, 0, d+k, e+k⟩ := by
  intro k; induction' k with k ih <;> intro A d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- R5+R2 single step: (0, b, 0, d+2, e+1) →* (0, b+2, 0, d, e)
theorem r5r2_step : ⟨0, b, 0, d+2, e+1⟩ [fm]⊢* ⟨0, b+2, 0, d, e⟩ := by
  step fm; step fm; finish

-- R5+R2 drain: (0, b, 0, d+2*k, e+k) →* (0, b+2*k, 0, d, e)
theorem r5r2_drain : ∀ k, ∀ b d e, ⟨0, b, 0, d+2*k, e+k⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  apply stepStar_trans (ih _ _ _)
  apply stepStar_trans r5r2_step; ring_nf; finish

-- Opening: (0, B+2, 0, 1, 1) →* (0, B, 2, 3, 0)
theorem opening : ⟨0, B+2, 0, 1, 1⟩ [fm]⊢* ⟨0, B, 2, 3, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  finish

-- R3,R1,R1 single round: (0, B+2, C+1, D, 0) →* (0, B, C+2, D+2, 0)
theorem r3r1r1_round : ⟨0, B+2, C+1, D, 0⟩ [fm]⊢* ⟨0, B, C+2, D+2, 0⟩ := by
  step fm; step fm; step fm; finish

-- R3,R1,R1 chain: (0, B+2*k, C+1, D, 0) →* (0, B, C+1+k, D+2*k, 0)
theorem r3r1r1_chain : ∀ k, ∀ B C D, ⟨0, B+2*k, C+1, D, 0⟩ [fm]⊢* ⟨0, B, C+1+k, D+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro B C D
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2) + 2 * k from by ring]
  apply stepStar_trans (ih _ _ _)
  rw [show C + 1 + k = (C + k) + 1 from by ring]
  apply stepStar_trans r3r1r1_round; ring_nf; finish

-- R3 chain: (A, 0, c+k, d, 0) →* (A+2*k, 0, c, d, 0)
theorem r3_chain : ∀ k, ∀ A c d, ⟨A, 0, c+k, d, 0⟩ [fm]⊢* ⟨A+2*k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro A c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- Main transition: (a+2, 0, 0, a+1, 0) →⁺ (2*a+4, 0, 0, 2*a+3, 0)
theorem main_trans : ⟨a+2, 0, 0, a+1, 0⟩ [fm]⊢⁺ ⟨2*a+4, 0, 0, 2*a+3, 0⟩ := by
  -- First R4 step for ⊢⁺, then ⊢* for the rest
  rw [show a + 2 = (a + 1) + 1 from by ring]; step fm
  -- Now at (a+1, 0, 0, a+1+1, 1): remaining R4 chain (a+1 steps)
  rw [show a + 1 = 0 + (a + 1) from by ring]
  apply stepStar_trans (r4_chain (a+1) _ _ _)
  -- Now at (0, 0, 0, 0+(a+1)+1+(a+1), 1+(a+1))
  -- Phase 2: R5+R2 drain (a+1 pairs)
  rw [show 0 + (a + 1) + 1 + (a + 1) = 1 + 2 * (a + 1) from by ring]
  apply stepStar_trans (r5r2_drain (a+1) _ _ _)
  -- Now at (0, 0+2*(a+1), 0, 1, 1)
  -- Phase 3: Opening
  rw [show 0 + 2 * (a + 1) = 2 * a + 2 from by ring]
  apply stepStar_trans (@opening (2 * a))
  -- Phase 4: R3,R1,R1 chain (a rounds)
  rw [show (2 : ℕ) * a = 0 + 2 * a from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain a _ _ _)
  -- Phase 5: R3 chain
  rw [show 1 + 1 + a = 0 + (a + 2) from by ring,
      show 3 + 2 * a = 2 * a + 3 from by ring]
  apply stepStar_trans (r3_chain (a+2) _ _ _)
  simp only [Nat.zero_add]; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, n+1, 0⟩) 0
  intro n; exists 2*n+2; exact main_trans

end Sz22_2003_unofficial_570
