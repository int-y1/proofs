import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1174: [5/6, 49/2, 44/35, 3/11, 1/5, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  1  0  0 -1
 0  0 -1  0  0
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1174

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: move e to b when a=0 and c=0.
theorem e_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- Interleave even: k rounds of R1,R1,R3 draining 2 from b each round.
theorem interleave_even : ∀ k, ∀ c d e,
    ⟨2, 2 * k, c, d + k, e⟩ [fm]⊢* ⟨2, 0, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- Interleave odd: k rounds of R1,R1,R3 then one final R1.
theorem interleave_odd : ∀ k, ∀ c d e,
    ⟨2, 2 * k + 1, c, d + k, e⟩ [fm]⊢* ⟨1, 0, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- R2,R2,R3 drain: consume c, each round adding 3 to d and 1 to e.
theorem r2_r3_drain : ∀ k, ∀ d e,
    ⟨2, 0, k, d, e⟩ [fm]⊢* ⟨2, 0, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    step fm
    step fm
    apply stepStar_trans (ih (d + 3) (e + 1))
    ring_nf; finish

-- R2 chain: drain a when b=0 and c=0.
theorem a_drain : ∀ a, ∀ d e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * a, e⟩ := by
  intro a; induction' a with a ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) e)
    ring_nf; finish

-- Main transition for even E.
-- Using m as the "excess" above 2*K+2 to avoid ℕ subtraction.
-- D = m + 2*K + 2, E = 2*K.
-- (0,0,0,m+2*K+2,2*K) →⁺ (0,0,0,m+4*K+4,2*K+1)
theorem main_even : ⟨0, 0, 0, m + 2 * K + 2, 2 * K⟩ [fm]⊢⁺
    ⟨0, 0, 0, m + 4 * K + 4, 2 * K + 1⟩ := by
  -- Phase 1: e_to_b
  apply stepStar_stepPlus_stepPlus
  · have := e_to_b (2 * K) 0 (m + 2 * K + 2) 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2+3: R6 then R3
  rw [show m + 2 * K + 2 = (m + 2 * K) + 1 + 1 from by ring]
  step fm  -- R6
  step fm  -- R3
  -- State: (2, 2*K, 0, m+2*K, 1)
  -- Phase 4: interleave_even
  rw [show m + 2 * K = (m + K) + K from by ring]
  apply stepStar_trans (interleave_even K 0 (m + K) 1)
  rw [show (0 : ℕ) + K = K from by ring]
  -- State: (2, 0, K, m+K, 1+K)
  -- Phase 5: r2_r3_drain
  apply stepStar_trans (r2_r3_drain K (m + K) (1 + K))
  -- State: (2, 0, 0, m+K+3*K, 1+K+K)
  -- Phase 6: a_drain
  apply stepStar_trans (a_drain 2 (m + K + 3 * K) (1 + K + K))
  ring_nf; finish

-- Main transition for odd E.
-- D = m + 2*K + 3, E = 2*K + 1.
-- (0,0,0,m+2*K+3,2*K+1) →⁺ (0,0,0,m+4*K+6,2*K+2)
theorem main_odd : ⟨0, 0, 0, m + 2 * K + 3, 2 * K + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, m + 4 * K + 6, 2 * K + 2⟩ := by
  -- Phase 1: e_to_b
  apply stepStar_stepPlus_stepPlus
  · have := e_to_b (2 * K + 1) 0 (m + 2 * K + 3) 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2+3: R6 then R3
  rw [show m + 2 * K + 3 = (m + 2 * K + 1) + 1 + 1 from by ring]
  step fm  -- R6
  step fm  -- R3
  -- State: (2, 2*K+1, 0, m+2*K+1, 1)
  -- Phase 4: interleave_odd
  rw [show m + 2 * K + 1 = (m + K + 1) + K from by ring]
  apply stepStar_trans (interleave_odd K 0 (m + K + 1) 1)
  rw [show (0 : ℕ) + K + 1 = K + 1 from by ring]
  -- State: (1, 0, K+1, m+K+1, 1+K)
  -- Phase 5: R2
  step fm
  -- State: (0, 0, K+1, m+K+3, 1+K)
  rw [show m + K + 1 + 2 = m + K + 3 from by ring]
  -- Phase 6: R3
  rw [show m + K + 3 = (m + K + 2) + 1 from by ring,
      show K + 1 = K + 1 from rfl]
  step fm
  -- State: (2, 0, K, m+K+2, K+2)
  rw [show 1 + K + 1 = K + 2 from by ring]
  -- Phase 7: r2_r3_drain
  apply stepStar_trans (r2_r3_drain K (m + K + 2) (K + 2))
  -- State: (2, 0, 0, m+K+2+3*K, K+2+K)
  -- Phase 8: a_drain
  apply stepStar_trans (a_drain 2 (m + K + 2 + 3 * K) (K + 2 + K))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ e + 2)
  · intro c ⟨d, e, hq, hd⟩; subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- e = 2*K (even)
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 * K + 2 := ⟨d - 2 * K - 2, by omega⟩
      exact ⟨⟨0, 0, 0, m + 4 * K + 4, 2 * K + 1⟩,
        ⟨m + 4 * K + 4, 2 * K + 1, rfl, by omega⟩,
        main_even⟩
    · -- e = 2*K + 1 (odd)
      subst hK
      obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 * K + 3 := ⟨d - 2 * K - 3, by omega⟩
      exact ⟨⟨0, 0, 0, m + 4 * K + 6, 2 * K + 2⟩,
        ⟨m + 4 * K + 6, 2 * K + 2, rfl, by omega⟩,
        main_odd⟩
  · exact ⟨2, 0, rfl, by omega⟩
