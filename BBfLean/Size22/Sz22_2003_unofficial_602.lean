import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #602: [35/6, 121/2, 4/55, 3/7, 28/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_602

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R1R1R3 chain: each round consumes 2 from b and 1 from e, adds 1 to c and 2 to d
theorem r1r1r3_chain : ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
  have many_step : ∀ k c d e, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- R3R2R2 chain: each round converts 1 from c to 3 in e
theorem r3r2r2_chain : ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+1+3*k⟩ := by
  have many_step : ∀ k c e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+1+3*k⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- Even transition: (0,0,0,2*K,E+K+1) →⁺ (0,0,0,2*K+1,E+3*K+4)
theorem even_trans : ⟨0, 0, 0, 2*K, E+K+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*K+1, E+3*K+4⟩ := by
  -- Phase 1: R4 x 2K → (0, 2K, 0, 0, E+K+1)
  rw [show 2*K = 0 + 2*K from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  simp only [Nat.zero_add]
  -- Phase 2: R5 → (2, 2K, 0, 1, E+K)
  rw [show E + K + 1 = (E + K) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Phase 3: R1R1R3 x K → (2, 0, K, 2K+1, E)
  rw [show 2 * K = 0 + 2 * K from by ring]
  apply stepStar_trans (@r1r1r3_chain 0 K 0 1 E)
  simp only [Nat.zero_add]
  -- Phase 4: R2R2 → (0, 0, K, 2K+1, E+4)
  step fm; step fm
  -- Phase 5: R3R2R2 x K → (0, 0, 0, 2K+1, E+4+3K)
  rw [show K = 0 + K from by ring, show E + 4 = (E + 3) + 1 from by ring]
  apply stepStar_trans r3r2r2_chain
  ring_nf; finish

-- Odd transition: (0,0,0,2*K+1,E+K+2) →⁺ (0,0,0,2*K+2,E+3*K+6)
theorem odd_trans : ⟨0, 0, 0, 2*K+1, E+K+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*K+2, E+3*K+6⟩ := by
  -- Phase 1: R4 x (2K+1) → (0, 2K+1, 0, 0, E+K+2)
  rw [show 2*K+1 = 0 + (2*K+1) from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  simp only [Nat.zero_add]
  -- Phase 2: R5 → (2, 2K+1, 0, 1, E+K+1)
  rw [show E + K + 2 = (E + K + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Phase 3: R1R1R3 x K → (2, 1, K, 2K+1, E+1)
  rw [show 2 * K + 1 = 1 + 2 * K from by ring,
      show E + K + 1 = (E + 1) + K from by ring]
  apply stepStar_trans (@r1r1r3_chain 1 K 0 1 (E + 1))
  simp only [Nat.zero_add]
  -- Phase 4: R1 → (1, 0, K+1, 2K+2, E+1)
  step fm
  -- Phase 5: R2 → (0, 0, K+1, 2K+2, E+3)
  step fm
  -- Phase 6: R3R2R2 x (K+1) → (0, 0, 0, 2K+2, E+3+3*(K+1))
  rw [show K + 1 = 0 + (K + 1) from by ring,
      show E + 3 = (E + 2) + 1 from by ring]
  apply stepStar_trans r3r2r2_chain
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ d + 2)
  · intro c ⟨d, e, hq, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = K + K = 2*K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨E, rfl⟩ : ∃ E, e = E + K + 1 := ⟨e - K - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 2*K+1, E+3*K+4⟩,
        ⟨2*K+1, E+3*K+4, rfl, by omega⟩, even_trans⟩
    · -- d odd: d = 2*K + 1
      subst hK
      obtain ⟨E, rfl⟩ : ∃ E, e = E + K + 2 := ⟨e - K - 2, by omega⟩
      exact ⟨⟨0, 0, 0, 2*K+2, E+3*K+6⟩,
        ⟨2*K+2, E+3*K+6, rfl, by omega⟩, odd_trans⟩
  · exact ⟨0, 2, rfl, by omega⟩
