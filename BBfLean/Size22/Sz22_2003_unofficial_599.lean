import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #599: [35/6, 121/2, 4/55, 3/7, 175/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 0  0  2  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_599

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem r4_chain : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R3R2R2 chain: each round does R3, R2, R2. Needs e≥1 for R3.
-- Net per round: c-=1, e+=3 (actually -1+4=+3 since e goes e+1 → e → e+2 → e+4)
theorem r3r2r2_chain : ∀ k c e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+4*k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  rw [show c + (k + 1) = c + k + 1 from by ring,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + k + 4 = (e + 4) + k from by ring]
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3R1R1 loop: each round does R3, R1, R1. Needs b≥2, c≥1, e≥1.
-- Net per round: b-=2, c+=1, d+=2, e-=1
theorem r3r1r1_chain : ∀ k c d e, ⟨0, b+2*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+1+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show b + 2 * (k + 1) = b + 2 * k + 1 + 1 from by ring,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Odd d transition: (0,0,0,2*K+1,E+2*K+5) →⁺ (0,0,0,2*K+2,E+4*K+11)
-- b=2*K+1 is odd, so K rounds R3R1R1 then R3,R1,R2
theorem trans_odd (K E : ℕ) :
    ⟨0, 0, 0, 2*K+1, E+2*K+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*K+2, E+4*K+11⟩ := by
  -- Phase 1: r4_chain
  rw [show (2 : ℕ)*K+1 = 0 + (2*K+1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2*K+1) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5: (0,2*K+1,0,0,E+2*K+5) → (0,2*K+1,2,1,E+2*K+4)
  rw [show E + 2*K + 5 = (E + 2*K + 4) + 1 from by ring]
  step fm
  -- Now: (0, 2*K+1, 2, 1, E+2*K+4) with 2*K+4 = 2*(K+1)+2
  -- Phase 3: K rounds R3R1R1
  -- (0, 2*K+1, 2, 1, E+2*K+4) = (0, 1+2*K, 1+1, 1, (E+K+4)+K)
  rw [show 2*K+1 = 1 + 2*K from by ring,
      show (2 : ℕ) = 1+1 from by ring,
      show E + 2*K + 4 = (E+K+4)+K from by ring]
  apply stepStar_trans (r3r1r1_chain K 1 1 (E+K+4))
  -- Now: (0, 1, 1+1+K, 1+2*K, E+K+4) = (0, 1, K+2, 2*K+1, E+K+4)
  rw [show 1 + 1 + K = (K + 1) + 1 from by ring,
      show 1 + 2*K = 2*K+1 from by ring]
  -- R3: (2, 1, K+1, 2*K+1, E+K+3)
  -- R1: (1, 0, K+2, 2*K+2, E+K+3)
  -- R2: (0, 0, K+2, 2*K+2, E+K+5)
  rw [show E+K+4 = (E+K+3)+1 from by ring]
  step fm; step fm; step fm
  -- Now: (0, 0, K+2, 2*K+2, E+K+5) = (0, 0, 0+(K+2), 2*K+2, (E+1)+(K+2)+2)
  -- Phase 4: r3r2r2_chain (K+2 rounds)
  rw [show K + 2 = 0 + (K+2) from by ring,
      show E+K+5 = (E+3)+(K+2) from by ring]
  apply stepStar_trans (r3r2r2_chain (K+2) 0 (E+3))
  ring_nf; finish

-- Even d transition: (0,0,0,2*(K+1),E+2*K+6) →⁺ (0,0,0,2*K+3,E+4*K+13)
-- b=2*(K+1) is even, so K+1 rounds R3R1R1
theorem trans_even (K E : ℕ) :
    ⟨0, 0, 0, 2*(K+1), E+2*K+6⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*K+3, E+4*K+13⟩ := by
  -- Phase 1: r4_chain
  rw [show 2*(K+1) = 0 + 2*(K+1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2*(K+1)) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5
  rw [show E + 2*K + 6 = (E + 2*K + 5) + 1 from by ring]
  step fm
  -- Now: (0, 2*(K+1), 2, 1, E+2*K+5)
  -- Phase 3: K+1 rounds R3R1R1
  rw [show 2*(K+1) = 0 + 2*(K+1) from by ring,
      show (2 : ℕ) = 1+1 from by ring,
      show E + 2*K + 5 = (E+K+4)+(K+1) from by ring]
  apply stepStar_trans (r3r1r1_chain (K+1) 1 1 (E+K+4))
  -- Now: (0, 0, 1+1+(K+1), 1+2*(K+1), E+K+4) = (0, 0, K+3, 2*K+3, E+K+4)
  rw [show 1 + 1 + (K + 1) = K + 3 from by ring,
      show 1 + 2 * (K + 1) = 2*K+3 from by ring]
  -- Phase 4: r3r2r2_chain (K+3 rounds)
  rw [show K + 3 = 0 + (K+3) from by ring,
      show E+K+4 = (E+1)+(K+3) from by ring]
  apply stepStar_trans (r3r2r2_chain (K+3) 0 (E+1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 7⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ 2 * d + 3)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = K + K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      -- d = 2*(k+1), need e ≥ 2*(2*(k+1))+3 = 4k+7
      -- Write e = E + 2*k + 6
      obtain ⟨E, rfl⟩ : ∃ E, e = E + 2*k + 6 := ⟨e - 2*k - 6, by omega⟩
      exact ⟨⟨0, 0, 0, 2*k+3, E+4*k+13⟩,
        ⟨2*k+3, E+4*k+13, rfl, by omega, by omega⟩,
        trans_even k E⟩
    · -- d odd: d = 2*K + 1
      subst hK
      -- d = 2*K+1, need e ≥ 2*(2*K+1)+3 = 4K+5
      -- Write e = E + 2*K + 5
      obtain ⟨E, rfl⟩ : ∃ E, e = E + 2*K + 5 := ⟨e - 2*K - 5, by omega⟩
      exact ⟨⟨0, 0, 0, 2*K+2, E+4*K+11⟩,
        ⟨2*K+2, E+4*K+11, rfl, by omega, by omega⟩,
        trans_odd K E⟩
  · exact ⟨1, 7, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_599
