import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #55: [35/6, 605/2, 4/77, 3/5, 7/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_55

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: c → b
theorem c_to_b : ∀ k, ∀ b c, ⟨0, b, c+k, 0, e⟩ [fm]⊢* ⟨0, b+k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R2R2R3 chain: (2, 0, C, D+k, E) →* (2, 0, C+2k, D, E+3k)
theorem r2r2r3_chain : ∀ k, ∀ C D E, ⟨2, 0, C, D+k, E⟩ [fm]⊢* ⟨2, 0, C+2*k, D, E+3*k⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · exists 0
  rw [show D + (k + 1) = (D + k) + 1 from by ring]
  step fm; step fm
  rw [show E + 4 = (E + 3) + 1 from by ring]
  step fm
  have h1 := ih (C + 2) D (E + 3)
  rw [show C + 2 + 2 * k = C + 2 * (k + 1) from by ring,
      show E + 3 + 3 * k = E + 3 * (k + 1) from by ring] at h1
  exact h1

-- R1R1R3 chain: (2, b+2k, C, D, E+k) →* (2, b, C+2k, D+k, E)
theorem r1r1r3_chain : ∀ k, ∀ C D E, ⟨2, b+2*k, C, D, E+k⟩ [fm]⊢* ⟨2, b, C+2*k, D+k, E⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm
  rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
  step fm
  rw [show D + 2 = (D + 1) + 1 from by ring]
  step fm
  have h1 := ih (C + 2) (D + 1) E
  rw [show C + 2 + 2 * k = C + 2 * (k + 1) from by ring,
      show D + 1 + k = D + (k + 1) from by ring] at h1
  exact h1

-- Final R2R2: (2, 0, C, 0, E) →* (0, 0, C+2, 0, E+4)
theorem final_r2r2 : ⟨2, 0, C, 0, E⟩ [fm]⊢* ⟨0, 0, C+2, 0, E+4⟩ := by
  step fm; step fm; finish

-- Even processing: n+1 = 2(K+1), n = 2K+1
-- (2, 2(K+1), 0, 0, 2K+1) →* (0, 0, 4K+6, 0, 4K+7)
theorem process_even (K : ℕ) : ⟨2, 2*(K+1), 0, 0, 2*K+1⟩ [fm]⊢* ⟨0, 0, 4*K+6, 0, 4*K+7⟩ := by
  -- R1R1R3 chain: b=0, k=K+1
  -- (2, 0+2(K+1), 0, 0, K+(K+1)) →* (2, 0, 2(K+1), K+1, K)
  apply stepStar_trans (c₂ := ⟨2, 0, 2*(K+1), K+1, K⟩)
  · have h := @r1r1r3_chain 0 (K+1) 0 0 K
    rw [show 0 + 2 * (K + 1) = 2 * (K + 1) from by ring,
        show K + (K + 1) = 2 * K + 1 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- R2R2R3 chain: k=K+1
  apply stepStar_trans (c₂ := ⟨2, 0, 4*K+4, 0, 4*K+3⟩)
  · have h := @r2r2r3_chain (K+1) (2*(K+1)) 0 K
    simp only [Nat.zero_add] at h
    rw [show 2 * (K + 1) + 2 * (K + 1) = 4 * K + 4 from by ring,
        show K + 3 * (K + 1) = 4 * K + 3 from by ring] at h
    exact h
  -- Final R2R2
  have h := @final_r2r2 (4*K+4) (4*K+3)
  rw [show 4 * K + 4 + 2 = 4 * K + 6 from by ring,
      show 4 * K + 3 + 4 = 4 * K + 7 from by ring] at h
  exact h

-- Odd processing K=0: (2, 1, 0, 0, 0) →* (0, 0, 4, 0, 5)
theorem process_odd_zero : ⟨2, 1, 0, 0, 0⟩ [fm]⊢* ⟨0, 0, 4, 0, 5⟩ := by
  -- R1: (1, 0, 1, 1, 0) → R2: (0, 0, 2, 1, 2) → R3: (2, 0, 2, 0, 1) → R2R2: (0, 0, 4, 0, 5)
  step fm; step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm; finish

-- Odd processing K≥1: n+1 = 2(K+1)+1, n = 2(K+1)
-- (2, 2(K+1)+1, 0, 0, 2(K+1)) →* (0, 0, 4(K+1)+4, 0, 4(K+1)+5)
theorem process_odd_pos (K : ℕ) : ⟨2, 2*(K+1)+1, 0, 0, 2*(K+1)⟩ [fm]⊢* ⟨0, 0, 4*(K+1)+4, 0, 4*(K+1)+5⟩ := by
  -- R1R1R3 ×(K+1) with b=1
  apply stepStar_trans (c₂ := ⟨2, 1, 2*(K+1), K+1, K+1⟩)
  · have h := @r1r1r3_chain 1 (K+1) 0 0 (K+1)
    rw [show 1 + 2 * (K + 1) = 2 * (K + 1) + 1 from by ring,
        show K + 1 + (K + 1) = 2 * (K + 1) from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Odd tail: (2, 1, 2(K+1), K+1, K+1) where K+1 = K+1 and K+1 = (K)+1
  -- R1R2R3: → (2, 0, 2(K+1)+2, K+1, K+2)
  apply stepStar_trans (c₂ := ⟨2, 0, 2*(K+1)+2, K+1, K+2⟩)
  · rw [show K + 1 = (K) + 1 from by ring]
    -- State: (2, 1, 2(K+1), K+1, K+1) = ((1)+1, (0)+1, 2(K+1), K+1, K+1)
    step fm
    -- After R1: (1, 0, 2(K+1)+1, K+2, K+1) = ((0)+1, 0, ...) → R2
    step fm
    -- After R2: (0, 0, 2(K+1)+2, K+2, K+3)
    -- R3: need K+2 = (K+1)+1 and K+3 = (K+2)+1
    rw [show K + 3 = (K + 2) + 1 from by ring, show K + 2 = (K + 1) + 1 from by ring]
    step fm; finish
  -- R2R2R3 ×(K+1): (2, 0, 2(K+1)+2, 0+(K+1), K+2)
  apply stepStar_trans (c₂ := ⟨2, 0, 4*(K+1)+2, 0, 4*(K+1)+1⟩)
  · have h := @r2r2r3_chain (K+1) (2*(K+1)+2) 0 (K+2)
    simp only [Nat.zero_add] at h
    rw [show 2 * (K + 1) + 2 + 2 * (K + 1) = 4 * (K + 1) + 2 from by ring,
        show K + 2 + 3 * (K + 1) = 4 * (K + 1) + 1 from by ring] at h
    exact h
  -- Final R2R2
  have h := @final_r2r2 (4*(K+1)+2) (4*(K+1)+1)
  rw [show 4 * (K + 1) + 2 + 2 = 4 * (K + 1) + 4 from by ring,
      show 4 * (K + 1) + 1 + 4 = 4 * (K + 1) + 5 from by ring] at h
  exact h

-- Main transition: (0, 0, c+1, 0, c+2) ⊢⁺ (0, 0, 2c+4, 0, 2c+5)
theorem main_trans (c : ℕ) : ⟨0, 0, c+1, 0, c+2⟩ [fm]⊢⁺ ⟨0, 0, 2*c+4, 0, 2*c+5⟩ := by
  -- Phase 1: c_to_b: (0, 0, 0+(c+1), 0, c+2) →* (0, c+1, 0, 0, c+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, c+1, 0, 0, c+2⟩)
  · have h := @c_to_b (c+2) (c+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5
  -- (0, c+1, 0, 0, c+2) → R5: (0, c+1, 0, 1, c+1)
  -- c+2 = (c+1)+1, so R5 matches: (0, c+1, 0, 0, (c+1)+1) = (a, b, c', d, e+1)
  -- with a=0, b=c+1, c'=0, d=0, e=c+1. Result: (0, c+1, 0, 1, c+1).
  apply step_stepPlus_stepPlus (c₂ := ⟨0, c+1, 0, 1, c+1⟩)
  · show fm ⟨0, c+1, 0, 0, (c+1)+1⟩ = some ⟨0, c+1, 0, 1, c+1⟩
    simp [fm]
  -- Phase 3: R3
  -- (0, c+1, 0, 1, c+1) → R3: (2, c+1, 0, 0, c)
  -- d+1=1, e+1=c+1 match R3. Result: (0+2, c+1, 0, 0, c).
  apply step_stepStar_stepPlus (c₂ := ⟨2, c+1, 0, 0, c⟩)
  · show fm ⟨0, c+1, 0, 0+1, c+1⟩ = some ⟨0+2, c+1, 0, 0, c⟩
    simp [fm]
  -- Now at (2, c+1, 0, 0, c). Split on parity of c+1.
  rcases Nat.even_or_odd (c + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- Even: c+1 = K+K = 2K
    rw [show K + K = 2 * K from by ring] at hK
    rcases K with _ | K
    · omega
    · -- c+1 = 2(K+1), c = 2K+1
      have hc : c = 2*K+1 := by omega
      subst hc; rw [hK]
      refine stepStar_trans (process_even K) ?_; ring_nf; finish
  · -- Odd: c+1 = 2K+1, c = 2K
    have hc : c = 2*K := by omega
    subst hc
    rcases K with _ | K
    · -- K=0: c=0, state (2, 1, 0, 0, 0)
      simp
      refine stepStar_trans process_odd_zero ?_; ring_nf; finish
    · -- K≥1: c=2(K+1), state (2, 2(K+1)+1, 0, 0, 2(K+1))
      refine stepStar_trans (process_odd_pos K) ?_; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨0, 0, n+1, 0, n+2⟩) 0
  intro n; exact ⟨2*n+3, main_trans n⟩
