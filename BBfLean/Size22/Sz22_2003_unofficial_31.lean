import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #31: [1/15, 27/77, 98/3, 5/7, 99/2]

Vector representation:
```
 0 -1 -1  0  0
 0  3  0 -1 -1
 1 -1  0  2  0
 0  0  1 -1  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_31

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R4 repeated: convert d to c
theorem d_to_c : ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  have many_step : ∀ k c, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro c
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k c

-- R3 repeated: convert b to a,d
theorem r3_chain : ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k, b, 0, d+2*k, 0⟩ := by
  have many_step : ∀ k a d, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k, b, 0, d+2*k, 0⟩ := by
    intro k; induction' k with k h <;> intro a d
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a d

-- Drain even c: (R5,R1,R1) repeated k times
theorem drain_c_even : ⟨a+k, 0, 2*k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  have many_step : ∀ k a e, ⟨a+k, 0, 2*k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a e

-- Drain odd c: (R5,R1,R1) repeated k times, then (R5,R1,R3)
theorem drain_c_odd : ⟨a+k+1, 0, 2*k+1, 0, e⟩ [fm]⊢* ⟨a+1, 0, 0, 2, e+k+1⟩ := by
  have many_step : ∀ k a e, ⟨a+k+1, 0, 2*k+1, 0, e⟩ [fm]⊢* ⟨a+1, 0, 0, 2, e+k+1⟩ := by
    intro k; induction' k with k h <;> intro a e
    · step fm; step fm; step fm; finish
    rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a e

-- R2,R2,R3 chain: (A, B, 0, 2, E) -> (A+B+3E, 0, 0, 2+2B+5E, 0)
theorem ab02e : ∀ E, ∀ A B, ⟨A, B, 0, 2, E⟩ [fm]⊢* ⟨A+B+3*E, 0, 0, 2+2*B+5*E, 0⟩ := by
  intro E; induction' E using Nat.strongRecOn with E ih; intro A B
  rcases E with _ | _ | E'
  · -- E=0: r3_chain
    rw [show 2 + 2 * B + 5 * 0 = 2 + 2 * B from by ring,
        show A + B + 3 * 0 = A + B from by ring]
    have h := @r3_chain A 0 B 2; rw [Nat.zero_add] at h
    exact h
  · -- E=1: R2, R3, r3_chain
    step fm; step fm
    have h := @r3_chain (A + 1) 0 (B + 2) 3; rw [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  · -- E'+2: R2, R2, R3, then IH for E'
    step fm; step fm; step fm
    apply stepStar_trans (ih E' (by omega) _ _)
    ring_nf; finish

-- Combined odd transition as ⊢*
theorem odd_star : ⟨m+K+1, 0, 0, 2*K+1, 0⟩ [fm]⊢* ⟨m+3*K+4, 0, 0, 5*K+7, 0⟩ := by
  -- Phase 1: d_to_c
  rw [show 2 * K + 1 = 0 + (2 * K + 1) from by ring]
  apply stepStar_trans (@d_to_c (m + K + 1) 0 0 (2 * K + 1))
  simp only [Nat.zero_add]
  -- Phase 2: drain_c_odd (e=0 so result has 0+K+1)
  rw [show (m + K + 1 : ℕ) = m + K + 1 from rfl]
  apply stepStar_trans (@drain_c_odd m K 0)
  -- Phase 3: ab02e (normalize 0+K+1 to K+1)
  rw [show 0 + K + 1 = K + 1 from by omega]
  apply stepStar_trans (ab02e (K + 1) (m + 1) 0)
  ring_nf; finish

theorem odd_trans : ⟨m+K+1, 0, 0, 2*K+1, 0⟩ [fm]⊢⁺ ⟨m+3*K+4, 0, 0, 5*K+7, 0⟩ := by
  apply stepStar_stepPlus odd_star
  intro h
  have := congr_arg (fun q : Q ↦ q.2.2.2.1) h
  simp at this
  omega

-- Combined even transition as ⊢*
theorem even_star : ⟨m+(K+1)+1, 0, 0, 2*(K+1), 0⟩ [fm]⊢* ⟨m+3*K+8, 0, 0, 5*K+14, 0⟩ := by
  -- Phase 1: d_to_c
  rw [show 2 * (K + 1) = 0 + 2 * (K + 1) from by ring]
  apply stepStar_trans (@d_to_c (m + (K + 1) + 1) 0 0 (2 * (K + 1)))
  simp only [Nat.zero_add]
  -- Phase 2: drain_c_even
  rw [show m + (K + 1) + 1 = (m + 1) + (K + 1) from by ring]
  apply stepStar_trans drain_c_even
  -- Phase 3: R5, R3 (2 steps); normalize 0+(K+1) first
  rw [show 0 + (K + 1) = K + 1 from by omega]
  step fm; step fm
  -- Phase 4: ab02e
  apply stepStar_trans (ab02e (K + 2) (m + 1) 1)
  ring_nf; finish

theorem even_trans : ⟨m+(K+1)+1, 0, 0, 2*(K+1), 0⟩ [fm]⊢⁺ ⟨m+3*K+8, 0, 0, 5*K+14, 0⟩ := by
  apply stepStar_stepPlus even_star
  intro h
  have := congr_arg (fun q : Q ↦ q.2.2.2.1) h
  simp at this
  omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 9, 0⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ 2 * a ≥ d + 1)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d even: d = K + K = 2*K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + (k + 1) + 1 := ⟨a - (k + 2), by omega⟩
      exact ⟨⟨m+3*k+8, 0, 0, 5*k+14, 0⟩,
        ⟨m+3*k+8, 5*k+14, rfl, by omega, by omega⟩, even_trans⟩
    · -- d odd: d = 2*K + 1
      subst hK
      obtain ⟨m, rfl⟩ : ∃ m, a = m + K + 1 := ⟨a - (K + 1), by omega⟩
      exact ⟨⟨m+3*K+4, 0, 0, 5*K+7, 0⟩,
        ⟨m+3*K+4, 5*K+7, rfl, by omega, by omega⟩, odd_trans⟩
  · exact ⟨5, 9, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_31
