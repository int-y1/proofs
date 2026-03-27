import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #598: [35/6, 121/2, 4/55, 3/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_598

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem r4_chain : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R3/R2/R2 chain: drain c while accumulating e
-- (0,0,c+1,d,e+1) -R3-> (2,0,c,d,e) -R2-> (1,0,c,d,e+2) -R2-> (0,0,c,d,e+4)
theorem r3r2r2_chain : ∀ k c e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+4*k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  rw [show c + (k + 1) = c + k + 1 from by ring,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + k + 4 = (e + 4) + k from by ring]
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- (R1,R1,R3) chain
theorem r1r1r3_chain : ∀ k b c D E, ⟨2, b+2*k, c, D, E+k⟩ [fm]⊢* ⟨2, b, c+k, D+2*k, E⟩ := by
  intro k; induction' k with k ih <;> intro b c D E
  · exists 0
  rw [show b + 2 * (k + 1) = b + 2 * k + 1 + 1 from by ring,
      show E + (k + 1) = E + k + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- Transition when d+2 is even: (0,0,0,2m+1,e+2m+3) ->+ (0,0,0,2m+2,e+4m+7)
theorem trans_even (m e : ℕ) :
    ⟨0, 0, 0, 2*m+1, e+2*m+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+2, e+4*m+7⟩ := by
  -- Phase 1: R4 (2m+1 times)
  rw [show (2 : ℕ)*m+1 = 0 + (2*m+1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2*m+1) 0)
  simp only [Nat.zero_add]
  -- Phase 2+3: R5, R3 -> (2, 2m+2, 0, 0, e+2m+1)
  step fm; step fm
  -- Phase 4: R1R1R3 chain (m+1 rounds)
  -- (2, 2*(m+1), 0, 0, e+2*m+1) = (2, 0+2*(m+1), 0, 0, (e+m)+(m+1))
  rw [show (2 : ℕ)*m+2 = 0 + 2*(m+1) from by ring,
      show e+2*m+1 = (e+m) + (m+1) from by ring]
  apply stepStar_trans (r1r1r3_chain (m+1) 0 0 0 (e+m))
  simp only [Nat.zero_add]
  -- State: (2, 0, m+1, 2*(m+1), e+m)
  -- R2, R2
  step fm; step fm
  -- State: (0, 0, m+1, 2*(m+1), e+m+4)
  -- r3r2r2 (m+1 rounds): (0, 0, 0+(m+1), 2*(m+1), (e+3)+(m+1))
  rw [show (m : ℕ)+1 = 0 + (m+1) from by ring,
      show e+m+4 = (e+3) + (m+1) from by ring]
  apply stepStar_trans (r3r2r2_chain (m+1) 0 (e+3))
  ring_nf; finish

theorem trans_odd (m e : ℕ) :
    ⟨0, 0, 0, 2*m+2, e+2*m+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+3, e+4*m+9⟩ := by
  -- Phase 1: R4 (2m+2 times)
  rw [show (2 : ℕ)*m+2 = 0 + (2*m+2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2*m+2) 0)
  simp only [Nat.zero_add]
  -- Phase 2+3: R5, R3 -> (2, 2m+3, 0, 0, e+2m+2)
  step fm; step fm
  -- Phase 4: R1R1R3 chain (m+1 rounds)
  -- (2, 2m+3, 0, 0, e+2m+2) = (2, 1+2*(m+1), 0, 0, (e+m+1)+(m+1))
  rw [show (2 : ℕ)*m+3 = 1 + 2*(m+1) from by ring,
      show e+2*m+2 = (e+m+1) + (m+1) from by ring]
  apply stepStar_trans (r1r1r3_chain (m+1) 1 0 0 (e+m+1))
  simp only [Nat.zero_add]
  -- State: (2, 1, m+1, 2*(m+1), e+m+1)
  -- R1: (1, 0, m+2, 2m+3, e+m+1)
  -- R2: (0, 0, m+2, 2m+3, e+m+3)
  step fm; step fm
  -- r3r2r2 (m+2 rounds): (0, 0, 0+(m+2), 2m+3, (e+1)+(m+2))
  rw [show (m : ℕ)+2 = 0 + (m+2) from by ring,
      show (2 : ℕ)*(m+1)+1 = 2*m+3 from by ring,
      show e+m+3 = (e+1) + (m+2) from by ring]
  apply stepStar_trans (r3r2r2_chain (m+2) 0 (e+1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 5⟩)
  · execute fm 8
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ d + 2)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = 2K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      -- d = 2*(m+1) = 2m+2, e >= 2m+4
      obtain ⟨f, rfl⟩ : ∃ f, e = f + 2*m + 4 := ⟨e - 2*m - 4, by omega⟩
      exact ⟨⟨0, 0, 0, 2*m+3, f+4*m+9⟩,
        ⟨2*m+3, f+4*m+9, rfl, by omega, by omega⟩, trans_odd m f⟩
    · -- d odd: d = 2K+1
      subst hK
      obtain ⟨f, rfl⟩ : ∃ f, e = f + 2*K + 3 := ⟨e - 2*K - 3, by omega⟩
      exact ⟨⟨0, 0, 0, 2*K+2, f+4*K+7⟩,
        ⟨2*K+2, f+4*K+7, rfl, by omega, by omega⟩, trans_even K f⟩
  · exact ⟨1, 5, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_598
