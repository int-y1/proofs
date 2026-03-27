import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #623: [35/6, 1331/2, 4/55, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  3
 2  0 -1  0 -1
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

---

Canonical states are `(0, 0, 0, d, e)` with `e ≥ d + 2`.
Each cycle increases `d` by 1 and `e` by `2*d + 4`:
`(0, 0, 0, d, e) →⁺ (0, 0, 0, d+1, e+2*d+4)`.
-/

namespace Sz22_2003_unofficial_623

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b+k, 0, 0, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b+k, 0, 0, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3+R2+R2 drain: convert c to e (net +5 per round)
theorem drain : ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+1+5*k⟩ := by
  have many_step : ∀ k c e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+1+5*k⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 3 + 3 = (e + 5) + 1 from by ring]
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- Interleaved R3+R1+R1 chain: each round consumes 2 from b, 1 from e
theorem r31_chain : ⟨0, b+2*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+1+k, d+2*k, e⟩ := by
  have many_step : ∀ k c d e, ⟨0, b+2*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+1+k, d+2*k, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- d=0 case: (0,0,0,0,e+2) →⁺ (0,0,0,1,e+6)
theorem zero_trans : ⟨0, 0, 0, 0, e+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, e+6⟩ := by
  rw [show e + 2 = e + 1 + 1 from by ring]
  step fm
  step fm; step fm; step fm
  ring_nf; finish

-- Even case: d = 2*(k+1)
theorem even_trans :
    ⟨0, 0, 0, 2*(k+1), e+k+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*k+3, e+5*k+11⟩ := by
  -- Phase 1: d_to_b: (0,0,0,2(k+1),E) →* (0,2(k+1),0,0,E)
  apply stepStar_stepPlus_stepPlus (@d_to_b 0 (2*(k+1)) (e+k+3))
  simp only [Nat.zero_add]
  -- Phase 2: R5: (0,2(k+1),0,0,E) → (0,2(k+1),1,1,E-1)
  rw [show e + k + 3 = e + k + 2 + 1 from by ring]
  step fm
  -- Phase 3: r31_chain (k+1 rounds):
  -- (0, 2(k+1), 1, 1, e+k+2) →* (0, 0, k+2, 2k+3, e+1)
  rw [show 2 * (k + 1) = 0 + 2 * (k + 1) from by ring,
      show e + k + 2 = (e + 1) + (k + 1) from by ring]
  apply stepStar_trans r31_chain
  simp only [Nat.zero_add]
  -- Phase 4: drain (k+2 rounds):
  -- (0, 0, k+2, 2k+3, e+1) →* (0, 0, 0, 2k+3, e+1+5*(k+2))
  rw [show 1 + (k + 1) = 0 + (k + 2) from by ring]
  apply stepStar_trans drain
  ring_nf; finish

-- Odd case: d = 2*k+1
theorem odd_trans :
    ⟨0, 0, 0, 2*k+1, e+k+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*k+2, e+5*k+8⟩ := by
  -- Phase 1: d_to_b
  apply stepStar_stepPlus_stepPlus (@d_to_b 0 (2*k+1) (e+k+2))
  simp only [Nat.zero_add]
  -- Phase 2: R5
  rw [show e + k + 2 = e + k + 1 + 1 from by ring]
  step fm
  -- Phase 3: r31_chain (k rounds)
  -- (0, 2k+1, 1, 1, e+k+1) →* (0, 1, k+1, 2k+1, e+1)
  rw [show 2 * k + 1 = 1 + 2 * k from by ring,
      show e + k + 1 = (e + 1) + k from by ring]
  apply stepStar_trans r31_chain
  simp only [Nat.zero_add]
  -- Phase 4: odd tail R3+R1+R2: (0,1,k+1,2k+1,e+1) → ... → (0,0,k+1,2k+2,e+4)
  rw [show 1 + k = k + 1 from by ring,
      show 1 + 2 * k = 2 * k + 1 from by ring]
  step fm; step fm; step fm
  -- Phase 5: drain (k+1 rounds)
  -- (0, 0, k+1, 2k+2, e+4) →* (0, 0, 0, 2k+2, e+4+5*(k+1))
  rw [show k + 1 = 0 + (k + 1) from by ring,
      show e + 3 = (e + 2) + 1 from by ring]
  apply stepStar_trans drain
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ e ≥ d + 2)
  · intro c ⟨d, e, hq, he⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = K + K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      rcases K with _ | K
      · -- K=0, d=0
        obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
        exact ⟨⟨0, 0, 0, 1, e'+6⟩, ⟨1, e'+6, rfl, by omega⟩, zero_trans⟩
      · -- K≥1, d=2*(K+1)
        obtain ⟨e', rfl⟩ : ∃ e', e = e' + K + 3 := ⟨e - K - 3, by omega⟩
        exact ⟨⟨0, 0, 0, 2*K+3, e'+5*K+11⟩,
          ⟨2*K+3, e'+5*K+11, rfl, by omega⟩, even_trans⟩
    · -- d odd: d = 2*K + 1
      subst hK
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + K + 2 := ⟨e - K - 2, by omega⟩
      exact ⟨⟨0, 0, 0, 2*K+2, e'+5*K+8⟩,
        ⟨2*K+2, e'+5*K+8, rfl, by omega⟩, odd_trans⟩
  · exact ⟨0, 3, rfl, by omega⟩

end Sz22_2003_unofficial_623
