import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #544: [28/15, 9/7, 1/6, 125/2, 6/5]

Vector representation:
```
 2 -1 -1  1
 0  2  0 -1
-1 -1  0  0
-1  0  3  0
 1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_544

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b+1, c, d⟩
  | _ => none

-- R4 chain: convert a to c (each step: a-1, c+3)
theorem r4_chain : ∀ k c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+3*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

-- 3-step round: R1 R1 R2 consuming 2 from c
theorem round3 : ∀ k, ∀ A C D, ⟨A, 2, C+2*k, D⟩ [fm]⊢* ⟨A+4*k, 2, C, D+k⟩ := by
  intro k; induction' k with k ih <;> intro A C D
  · exists 0
  rw [show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring]
  step fm; step fm
  rw [show D + 1 + 1 = (D + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R2 drain: convert d to b
theorem r2_drain : ∀ k, ∀ A b, ⟨A, b, 0, k⟩ [fm]⊢* ⟨A, b+2*k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A b
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 drain: consume a and b together
theorem r3_drain : ∀ k, ∀ A, ⟨A+k, k, 0, 0⟩ [fm]⊢* ⟨A, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

-- Full even cycle as ⊢*: (0, 0, 6*(m+1), 0) ->* (6*m+5, 0, 0, 0)
theorem even_cycle : ⟨0, 0, 6*(m+1), 0⟩ [fm]⊢* ⟨6*m+5, 0, 0, 0⟩ := by
  -- Opening R5 R1 R2 -> (3, 2, 6*m+4, 0)
  rw [show 6*(m+1) = (6*m+4) + 1 + 1 from by ring]
  step fm; step fm; step fm
  -- Chain of 3*m+2 rounds
  rw [show 6*m+4 = 0 + 2*(3*m+2) from by ring]
  apply stepStar_trans (round3 (3*m+2) 3 0 0)
  simp only [Nat.zero_add]
  -- R2 drain
  rw [show 3 + 4 * (3 * m + 2) = 12*m+11 from by ring]
  apply stepStar_trans (r2_drain (3*m+2) (12*m+11) 2)
  -- R3 drain
  rw [show 12*m+11 = (6*m+5) + (6*m+6) from by ring,
      show 2 + 2 * (3 * m + 2) = 6*m+6 from by ring]
  exact r3_drain (6*m+6) (6*m+5)

-- Full odd cycle as ⊢*: (0, 0, 6*m+9, 0) ->* (6*m+8, 0, 0, 0)
theorem odd_cycle : ⟨0, 0, 6*m+9, 0⟩ [fm]⊢* ⟨6*m+8, 0, 0, 0⟩ := by
  -- Opening R5 R1 R2
  rw [show 6*m+9 = (6*m+7) + 1 + 1 from by ring]
  step fm; step fm; step fm
  -- Chain of 3*m+3 rounds
  rw [show 6*m+7 = 1 + 2*(3*m+3) from by ring]
  apply stepStar_trans (round3 (3*m+3) 3 1 0)
  simp only [Nat.zero_add]
  -- R1 close
  rw [show 3 + 4 * (3 * m + 3) = 12*m+15 from by ring]
  step fm
  -- R2 drain
  rw [show 12 * m + 15 + 2 = 12*m+17 from by ring,
      show 3 * m + 3 + 1 = 3*m+4 from by ring]
  apply stepStar_trans (r2_drain (3*m+4) (12*m+17) 1)
  -- R3 drain
  rw [show 12*m+17 = (6*m+8) + (6*m+9) from by ring,
      show 1 + 2 * (3 * m + 4) = 6*m+9 from by ring]
  exact r3_drain (6*m+9) (6*m+8)

-- Even transition: (2*(m+1), 0, 0, 0) ->+ (6*m+5, 0, 0, 0)
theorem even_trans : ⟨2*(m+1), 0, 0, 0⟩ [fm]⊢⁺ ⟨6*m+5, 0, 0, 0⟩ := by
  -- First R4 step gives ⊢⁺
  rw [show 2*(m+1) = (2*m+1) + 1 from by ring]
  step fm
  -- Remaining R4 steps
  rw [show 2*m+1 = 0 + (2*m+1) from by ring]
  apply stepStar_trans (r4_chain (2*m+1) 3)
  rw [show 3 + 3 * (2 * m + 1) = 6*(m+1) from by ring]
  exact even_cycle

-- Odd transition: (2*m+3, 0, 0, 0) ->+ (6*m+8, 0, 0, 0)
theorem odd_trans : ⟨2*m+3, 0, 0, 0⟩ [fm]⊢⁺ ⟨6*m+8, 0, 0, 0⟩ := by
  -- First R4 step gives ⊢⁺
  rw [show 2*m+3 = (2*m+2) + 1 from by ring]
  step fm
  -- Remaining R4 steps
  rw [show 2*m+2 = 0 + (2*m+2) from by ring]
  apply stepStar_trans (r4_chain (2*m+2) 3)
  rw [show 3 + 3 * (2 * m + 2) = 6*m+9 from by ring]
  exact odd_cycle

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩)
  · execute fm 9
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a, q = ⟨a, 0, 0, 0⟩ ∧ a ≥ 2)
  · intro c ⟨a, hq, ha⟩; subst hq
    rcases Nat.even_or_odd a with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      exact ⟨⟨6*m+5, 0, 0, 0⟩, ⟨6*m+5, rfl, by omega⟩, even_trans⟩
    · subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      rw [show 2 * (m + 1) + 1 = 2*m+3 from by ring]
      exact ⟨⟨6*m+8, 0, 0, 0⟩, ⟨6*m+8, rfl, by omega⟩, odd_trans⟩
  · exact ⟨2, rfl, by omega⟩
