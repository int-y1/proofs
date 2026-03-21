import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #88: [5/6, 539/2, 44/35, 3/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  1
 0  1  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_88

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: e → b (when a=0, c=0)
theorem e_to_b : ∀ k, ∀ b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b+k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [show b + (k + 1) = (b + 1) + k from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1R1R3 interleave: each round consumes 2 from B, 1 from D, adds 1 to C and E.
-- Generalized to work with any starting B value (not just 0).
theorem r1r1r3_rounds : ∀ k, ∀ B C D E, ⟨2, B+2*k, C, D+k, E⟩ [fm]⊢* ⟨2, B, C+k, D, E+k⟩ := by
  intro k; induction' k with k h <;> intro B C D E
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k + 1) + 1 from by ring,
      show D + (k + 1) = (D + k) + 1 from by ring]
  -- R1: a+1=2, b+1=B+2k+1+1
  step fm
  rw [show B + 2 * k + 1 = (B + 2 * k) + 1 from by ring]
  -- R1: a+1=1+1, b+1=B+2k+1
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring,
      show D + k + 1 = (D + k) + 1 from by ring]
  -- R3: c+1=C+2, d+1=D+k+1
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R3R2R2 chain: from (0, 0, k, D+1, E) to (0, 0, 0, D+1+3*k, E+3*k)
theorem r3r2r2_chain : ∀ k, ∀ D E, ⟨0, 0, k, D+1, E⟩ [fm]⊢* ⟨0, 0, 0, D+1+3*k, E+3*k⟩ := by
  intro k; induction' k with k h <;> intro D E
  · exists 0
  rw [show (k : ℕ) + 1 = k + 1 from rfl]
  -- R3: c+1=k+1, d+1=D+1
  step fm
  -- R2: a+1=2
  step fm
  -- R2: a+1=1
  step fm
  rw [show D + 4 = (D + 3) + 1 from by ring]
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Even case: (0, 2k, 0, d+k+2, 0) ⊢+ (0, 4k+3, 0, d+3k+4, 0)
theorem trans_even : ∀ k d, ⟨0, 2*k, 0, d+k+2, 0⟩ [fm]⊢⁺ ⟨0, 4*k+3, 0, d+3*k+4, 0⟩ := by
  intro k d
  -- R5: (0, 2k, 0, d+k+2, 0) -> (0, 2k, 1, d+k+1, 0)
  rw [show d + k + 2 = (d + k + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*k, 1, d+k+1, 0⟩)
  · show fm ⟨0, 2*k, 0, (d + k + 1) + 1, 0⟩ = some ⟨0, 2*k, 1, d+k+1, 0⟩; simp [fm]
  -- R3: (0, 2k, 1, d+k+1, 0) -> (2, 2k, 0, d+k, 1)
  apply stepStar_trans (c₂ := ⟨2, 2*k, 0, d+k, 1⟩)
  · rw [show d + k + 1 = (d + k) + 1 from by ring]
    step fm; finish
  -- R1R1R3 interleave k rounds: (2, 0+2k, 0, d+k, 1) ->* (2, 0, k, d, 1+k)
  apply stepStar_trans (c₂ := ⟨2, 0, k, d, 1+k⟩)
  · have h := r1r1r3_rounds k 0 0 d 1
    simp only [Nat.zero_add] at h; exact h
  -- R2: (2, 0, k, d, 1+k) -> (1, 0, k, d+2, 1+k+1)
  -- R2: -> (0, 0, k, d+2+2, 1+k+1+1)
  -- R3R2R2 chain k rounds
  apply stepStar_trans (c₂ := ⟨0, 0, 0, d+3*k+4, 4*k+3⟩)
  · step fm; step fm
    -- Goal: (0, 0, k, d+2+2, 1+k+1+1) ⊢* (0, 0, 0, d+3*k+4, 4*k+3)
    rw [show d + 2 + 2 = (d + 3) + 1 from by ring]
    have h := r3r2r2_chain k (d+3) (1+k+1+1)
    rw [show d + 3 + 1 + 3 * k = d + 3 * k + 4 from by ring,
        show 1 + k + 1 + 1 + 3 * k = 4 * k + 3 from by ring] at h
    exact h
  -- R4 chain: (0, 0, 0, d+3k+4, 4k+3) ->* (0, 4k+3, 0, d+3k+4, 0)
  have h := e_to_b (4*k+3) 0 (d+3*k+4)
  simp only [Nat.zero_add] at h; exact h

-- Odd case: (0, 2k+1, 0, d+k+2, 0) ⊢+ (0, 4k+5, 0, d+3k+5, 0)
theorem trans_odd : ∀ k d, ⟨0, 2*k+1, 0, d+k+2, 0⟩ [fm]⊢⁺ ⟨0, 4*k+5, 0, d+3*k+5, 0⟩ := by
  intro k d
  -- R5: (0, 2k+1, 0, d+k+2, 0) -> (0, 2k+1, 1, d+k+1, 0)
  rw [show d + k + 2 = (d + k + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*k+1, 1, d+k+1, 0⟩)
  · show fm ⟨0, 2*k+1, 0, (d + k + 1) + 1, 0⟩ = some ⟨0, 2*k+1, 1, d+k+1, 0⟩; simp [fm]
  -- R3: (0, 2k+1, 1, d+k+1, 0) -> (2, 2k+1, 0, d+k, 1)
  apply stepStar_trans (c₂ := ⟨2, 2*k+1, 0, d+k, 1⟩)
  · rw [show d + k + 1 = (d + k) + 1 from by ring]
    step fm; finish
  -- R1R1R3 interleave k rounds: (2, 1+2k, 0, d+k, 1) ->* (2, 1, k, d, 1+k)
  apply stepStar_trans (c₂ := ⟨2, 1, k, d, 1+k⟩)
  · rw [show 2 * k + 1 = 1 + 2 * k from by ring]
    have h := r1r1r3_rounds k 1 0 d 1
    simp only [Nat.zero_add] at h; exact h
  -- R1: (2, 1, k, d, 1+k) -> (1, 0, k+1, d, 1+k)
  apply stepStar_trans (c₂ := ⟨1, 0, k+1, d, 1+k⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  -- R2: (1, 0, k+1, d, 1+k) -> (0, 0, k+1, d+2, 1+k+1)
  -- R3R2R2 chain (k+1) rounds
  apply stepStar_trans (c₂ := ⟨0, 0, 0, d+3*k+5, 4*k+5⟩)
  · step fm
    -- Goal: (0, 0, k+1, d+2, 1+k+1) ⊢* (0, 0, 0, d+3*k+5, 4*k+5)
    rw [show d + 2 = (d + 1) + 1 from by ring]
    have h := r3r2r2_chain (k+1) (d+1) (1+k+1)
    rw [show d + 1 + 1 + 3 * (k + 1) = d + 3 * k + 5 from by ring,
        show 1 + k + 1 + 3 * (k + 1) = 4 * k + 5 from by ring] at h
    exact h
  -- R4 chain: (0, 0, 0, d+3k+5, 4k+5) ->* (0, 4k+5, 0, d+3k+5, 0)
  have h := e_to_b (4*k+5) 0 (d+3*k+5)
  simp only [Nat.zero_add] at h; exact h

-- Main transition: (0, b, 0, d, 0) with 2d ≥ b+3 ⊢+ (0, 2b+3, 0, b+d+2, 0) with 2(b+d+2) ≥ (2b+3)+3
theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1, 0, 0, 0, 0) ->2 (0, 1, 0, 2, 0)
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 2, 0⟩) (by execute fm 2)
  -- Use progress_nonhalt with predicate P
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b d, q = ⟨0, b, 0, d, 0⟩ ∧ 2 * d ≥ b + 3)
  · -- Progress: ∀ c, P c → ∃ c', P c' ∧ c ⊢+ c'
    intro c ⟨b, d, hq, hbd⟩
    subst hq
    -- Case split on parity of b
    rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- Even: b = k + k
      subst hk
      have hdk : d ≥ k + 2 := by omega
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + k + 2 := ⟨d - k - 2, by omega⟩
      refine ⟨⟨0, 4*k+3, 0, d'+3*k+4, 0⟩, ⟨4*k+3, d'+3*k+4, rfl, by omega⟩, ?_⟩
      rw [show k + k = 2 * k from by ring]
      exact trans_even k d'
    · -- Odd: b = 2k + 1
      subst hk
      have hdk : d ≥ k + 2 := by omega
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + k + 2 := ⟨d - k - 2, by omega⟩
      refine ⟨⟨0, 4*k+5, 0, d'+3*k+5, 0⟩, ⟨4*k+5, d'+3*k+5, rfl, by omega⟩, ?_⟩
      exact trans_odd k d'
  · -- Initial state satisfies P: (0, 1, 0, 2, 0) with 2*2 ≥ 1+3
    exact ⟨1, 2, rfl, by omega⟩
