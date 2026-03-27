import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #58: [1/15, 9/77, 98/3, 5/7, 99/2]

Vector representation:
```
 0 -1 -1  0  0
 0  2  0 -1 -1
 1 -1  0  2  0
 0  0  1 -1  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_58

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R4 chain: d → c
theorem r4_chain : ∀ k, ∀ a c d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1) d)
  ring_nf; finish

-- R3 chain: b → a, d
theorem r3_chain : ∀ k, ∀ a b d, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k, b, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (a + 1) b (d + 2))
  ring_nf; finish

-- Even drain: R5, R1, R1 repeated k times
theorem even_drain : ∀ k, ∀ a c e, ⟨a+k, 0, c+2*k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih a c (e + 1))
  ring_nf; finish

-- Build-up: (a, b+1, 0, 0, e) ⊢* (a + 2*e + b + 1, 0, 0, 3*e + 2*b + 2, 0)
theorem buildup : ∀ e, ∀ a b, ⟨a, b+1, 0, 0, e⟩ [fm]⊢* ⟨a+2*e+b+1, 0, 0, 3*e+2*b+2, 0⟩ := by
  intro e; induction' e using Nat.strongRecOn with e ih
  intro a b
  rcases e with _ | _ | e
  · -- e = 0: R3 chain
    have h := r3_chain (b + 1) a 0 0
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  · -- e = 1: R3, R2, then R3 chain
    step fm; step fm
    have h := r3_chain (b + 2) (a + 1) 0 1
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  · -- e + 2: R3, R2, R2 then IH with e
    rw [show (e + 1 + 1 : ℕ) = e + 2 from by ring]
    step fm; step fm; step fm
    rw [show b + 1 + 1 + 2 = (b + 3) + 1 from by ring]
    have h := ih e (by omega) (a + 1) (b + 3)
    refine stepStar_trans h ?_; ring_nf; finish

-- Even d transition: (α+K+2, 0, 0, 2*K+2, 0) ⊢⁺ (α+2*K+6, 0, 0, 3*K+10, 0)
theorem trans_even (α K : ℕ) :
    ⟨α+K+2, 0, 0, 2*K+2, 0⟩ [fm]⊢⁺ ⟨α+2*K+6, 0, 0, 3*K+10, 0⟩ := by
  -- Phase 1: R4 chain
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨α+K+2, 0, 2*K+2, 0, 0⟩)
  · have h := r4_chain (2*K+2) (α+K+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: Even drain K+1 rounds
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨α+1, 0, 0, 0, K+1⟩)
  · have h := even_drain (K+1) (α+1) 0 0
    simp only [Nat.zero_add] at h
    rw [show α + 1 + (K + 1) = α + K + 2 from by ring,
        show 2 * (K + 1) = 2 * K + 2 from by ring] at h; exact h
  -- Phase 3: R5, R3, R2, R2 (4 steps giving ⊢⁺)
  apply step_stepStar_stepPlus
  · show fm ⟨α+1, 0, 0, 0, K+1⟩ = some ⟨α, 2, 0, 0, K+2⟩; simp [fm]
  step fm; step fm; step fm
  -- Now at (α+1, 5, 0, 0, K) = (α+1, 4+1, 0, 0, K)
  rw [show (5 : ℕ) = 4 + 1 from by ring]
  have h := buildup K (α + 1) 4
  refine stepStar_trans h ?_; ring_nf; finish

-- Odd d transition: (α+K+2, 0, 0, 2*K+3, 0) ⊢⁺ (α+2*K+5, 0, 0, 3*K+8, 0)
theorem trans_odd (α K : ℕ) :
    ⟨α+K+2, 0, 0, 2*K+3, 0⟩ [fm]⊢⁺ ⟨α+2*K+5, 0, 0, 3*K+8, 0⟩ := by
  -- Phase 1: R4 chain
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨α+K+2, 0, 2*K+3, 0, 0⟩)
  · have h := r4_chain (2*K+3) (α+K+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: Even drain K+1 rounds (leaving c=1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨α+1, 0, 1, 0, K+1⟩)
  · have h := even_drain (K+1) (α+1) 1 0
    simp only [Nat.zero_add] at h
    rw [show α + 1 + (K + 1) = α + K + 2 from by ring,
        show 1 + 2 * (K + 1) = 2 * K + 3 from by ring] at h; exact h
  -- Phase 3: R5, R1, R3, R2, R2 (5 steps giving ⊢⁺)
  apply step_stepStar_stepPlus
  · show fm ⟨α+1, 0, 1, 0, K+1⟩ = some ⟨α, 2, 1, 0, K+2⟩; simp [fm]
  step fm; step fm; step fm; step fm
  -- Now at (α+1, 4, 0, 0, K) = (α+1, 3+1, 0, 0, K)
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  have h := buildup K (α + 1) 3
  refine stepStar_trans h ?_; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 7, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 5 ∧ 2 * a ≥ d + 1)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- d = 2K (even), K ≥ 3 since d ≥ 6
      subst hK
      -- K ≥ 1, so 2K = 2*(K-1)+2 = 2*(K-1+1)
      -- Use trans_even with α = a-K-1, K' = K-1
      -- But we need to rewrite to match trans_even's signature
      rw [show K + K = 2 * (K - 1) + 2 from by omega]
      refine ⟨_, ⟨a + K + 3, 3 * (K - 1) + 10, rfl, by omega, by omega⟩, ?_⟩
      have h := trans_even (a - K - 1) (K - 1)
      rw [show a - K - 1 + (K - 1) + 2 = a from by omega,
          show 2 * (K - 1) + 2 = 2 * (K - 1) + 2 from rfl,
          show a - K - 1 + 2 * (K - 1) + 6 = a + K + 3 from by omega] at h
      convert h using 2
    · -- d = 2K + 1 (odd), K ≥ 2 since d ≥ 5
      subst hK
      -- 2K+1 = 2*(K-1)+3
      rw [show 2 * K + 1 = 2 * (K - 1) + 3 from by omega]
      refine ⟨_, ⟨a + K + 2, 3 * (K - 1) + 8, rfl, by omega, by omega⟩, ?_⟩
      have h := trans_odd (a - K - 1) (K - 1)
      rw [show a - K - 1 + (K - 1) + 2 = a from by omega,
          show 2 * (K - 1) + 3 = 2 * (K - 1) + 3 from rfl,
          show a - K - 1 + 2 * (K - 1) + 5 = a + K + 2 from by omega] at h
      convert h using 2
  · exact ⟨4, 7, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_58
