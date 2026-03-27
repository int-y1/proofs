import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #606: [35/6, 121/2, 4/55, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_606

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · finish
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R1R1R3 chain: 3 steps per round, consuming 2 from b and 1 from e
theorem r1r1r3_chain : ⟨2, 2 * k + b, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
  have many_step : ∀ k c d e, ⟨2, 2 * k + b, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · simp; finish
    rw [show 2 * (k + 1) + b = (2 * k + b) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- R2R2R3 drain: 3 steps per round, consuming 1 from c and adding 3 to e
theorem r2r2r3_drain : ⟨2, 0, c + k, d, e⟩ [fm]⊢* ⟨2, 0, c, d, e + 3 * k⟩ := by
  have many_step : ∀ k c e, ⟨2, 0, c + k, d, e⟩ [fm]⊢* ⟨2, 0, c, d, e + 3 * k⟩ := by
    intro k; induction' k with k h <;> intro c e
    · simp; finish
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- Combined even body: full transition for even b = 2*(k+1)
-- (0, 2*(k+1), 0, 0, e+(k+1)+2) ->+ (0, 0, 0, 2*(k+1)+1, e+3*(k+1)+4)
theorem even_body :
    ⟨0, 2 * (k + 1), 0, 0, e + (k + 1) + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (k + 1) + 1, e + 3 * (k + 1) + 4⟩ := by
  -- Opening R5+R1+R3
  step fm; step fm; step fm
  -- After: (2, 2*(k+1), 0, 1, e+(k+1))
  -- R1R1R3 chain (k+1 rounds)
  apply stepStar_trans (@r1r1r3_chain (k + 1) 0 0 1 e)
  -- After: (2, 0, 0+(k+1), 1+2*(k+1), e)
  -- Need to normalize d component: 1+2*(k+1) = 2*(k+1)+1
  show (2, 0, 0 + (k + 1), 1 + 2 * (k + 1), e) [fm]⊢* ⟨0, 0, 0, 2 * (k + 1) + 1, e + 3 * (k + 1) + 4⟩
  rw [show 1 + 2 * (k + 1) = 2 * (k + 1) + 1 from by ring]
  -- R2R2R3 drain (k+1 rounds)
  apply stepStar_trans (@r2r2r3_drain 0 (k + 1) (2 * (k + 1) + 1) e)
  -- After: (2, 0, 0, 2*(k+1)+1, e+3*(k+1))
  -- Final R2R2
  step fm; step fm
  ring_nf; finish

-- Combined odd body: full transition for odd b = 2*k+1
-- (0, 2*k+1, 0, 0, e+k+2) ->+ (0, 0, 0, 2*k+2, e+3*k+5)
theorem odd_body :
    ⟨0, 2 * k + 1, 0, 0, e + k + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 2, e + 3 * k + 5⟩ := by
  -- Opening R5+R1+R3
  step fm; step fm; step fm
  -- After: (2, 2*k+1, 0, 1, e+k)
  -- R1R1R3 chain (k rounds)
  apply stepStar_trans (@r1r1r3_chain k 1 0 1 e)
  -- After: (2, 1, 0+k, 1+2*k, e)
  -- Odd cleanup: R1+R2+R3
  show (2, 1, 0 + k, 1 + 2 * k, e) [fm]⊢* ⟨0, 0, 0, 2 * k + 2, e + 3 * k + 5⟩
  step fm; step fm; step fm
  -- After: (2, 0, 0+k, 1+2*k+1, e+1) = (2, 0, k, 2*k+2, e+1)
  show (2, 0, 0 + k, 1 + 2 * k + 1, e + 1) [fm]⊢* ⟨0, 0, 0, 2 * k + 2, e + 3 * k + 5⟩
  rw [show 1 + 2 * k + 1 = 2 * k + 2 from by ring]
  -- R2R2R3 drain (k rounds)
  apply stepStar_trans (@r2r2r3_drain 0 k (2 * k + 2) (e + 1))
  -- After: (2, 0, 0, 2*k+2, e+1+3*k)
  -- Final R2R2
  step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d E, q = ⟨0, 0, 0, d + 1, E⟩ ∧ E ≥ d + 2)
  · intro c ⟨d, E, hq, hE⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = 2K, b = d+1 = 2K+1 (odd body)
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨e, rfl⟩ : ∃ e, E = e + K + 2 := ⟨E - K - 2, by omega⟩
      refine ⟨⟨0, 0, 0, 2 * K + 2, e + 3 * K + 5⟩,
        ⟨2 * K + 1, e + 3 * K + 5, by ring_nf, by omega⟩, ?_⟩
      -- (0, 0, 0, 2K+1, e+K+2) ->+ (0, 0, 0, 2K+2, e+3K+5)
      rw [show 2 * K + 1 = 0 + (2 * K + 1) from by ring]
      apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0) (e := e + K + 2))
      simp only [Nat.zero_add]
      exact odd_body
    · -- d odd: d = 2K+1, b = d+1 = 2(K+1) (even body)
      subst hK
      obtain ⟨e, rfl⟩ : ∃ e, E = e + (K + 1) + 2 := ⟨E - K - 3, by omega⟩
      refine ⟨⟨0, 0, 0, 2 * (K + 1) + 1, e + 3 * (K + 1) + 4⟩,
        ⟨2 * (K + 1), e + 3 * (K + 1) + 4, by ring_nf, by omega⟩, ?_⟩
      -- (0, 0, 0, 2K+2, e+(K+1)+2) ->+ (0, 0, 0, 2(K+1)+1, e+3(K+1)+4)
      rw [show 2 * K + 1 + 1 = 0 + (2 * (K + 1)) from by ring]
      apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0) (e := e + (K + 1) + 2))
      simp only [Nat.zero_add]
      exact even_body
  · exact ⟨0, 4, rfl, by omega⟩
