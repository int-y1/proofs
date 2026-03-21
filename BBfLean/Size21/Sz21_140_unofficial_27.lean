import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #27: [35/6, 11/2, 4/55, 3/7, 28/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_27

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R2 repeated: a → e (when b=0, c=0)
theorem a_to_e : ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+k⟩ := by
  have many_step : ∀ k a e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a e

-- R4 repeated: d → b (when a=0, c=0)
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- R3R2R2 chain: each round (0, 0, c+1, D, e) → (0, 0, c, D, e+1) in 3 steps
-- Requires c+k >= 1 and e >= 1
theorem r3r2r2_chain : ∀ k, ∀ c e, ⟨0, 0, c+k, D, e+k⟩ [fm]⊢* ⟨0, 0, c, D, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R3: (0, 0, (c+k)+1, D, (e+k)+1) → (2, 0, c+k, D, e+k)
  step fm  -- R2: (2, 0, c+k, D, e+k) → (1, 0, c+k, D, e+k+1)
  step fm  -- R2: (1, 0, c+k, D, e+k+1) → (0, 0, c+k, D, e+k+2)
  rw [show e + k + 1 + 1 = (e + 2) + k from by ring]
  apply stepStar_trans (h c (e + 2))
  ring_nf; finish

-- One R1R1R3 round: (2, B+2, C, D+1, B+C+2) → (2, B, C+1, D+3, B+C+1) in 3 steps
theorem r1r1r3_one : ⟨2, B+2, C, D+1, B+C+2⟩ [fm]⊢⁺ ⟨2, B, C+1, D+3, B+C+1⟩ := by
  rw [show B + 2 = (B + 1) + 1 from by ring]
  step fm  -- R1: (2, (B+1)+1, C, D+1, B+C+2) → (1, B+1, C+1, D+2, B+C+2)
  -- Now a=1, b=B+1 >= 1, so R1 fires again... wait, B+1 >= 1 only if we show it
  -- Actually a=1 >= 1 and b=B+1... but R1 needs a+1 and b+1 patterns
  -- After R1: (1, B+1, C+1, D+2, B+C+2)
  -- R1 matches: a+1=1 means a=0 won't work for R1. Actually a=1=0+1, b=B+1=(B)+1
  -- So R1: (0+1, B+1, C+1, D+2, B+C+2) → wait, this needs a >= 1 AND b >= 1
  -- a=1 >= 1, b=B+1 >= 1, so R1: (0, B, C+2, D+3, B+C+2)
  rw [show B + C + 2 = B + (C + 2) from by ring]
  step fm  -- R1: (1, B+1, C+1, D+2, B+C+2) → (0, B, C+2, D+3, B+C+2)
  -- Now a=0, c=C+2 >= 1, e=B+C+2 >= 1 (assuming B+C >= 0, which is always true... but e >= 1 needs B+C+2 >= 1, always true)
  -- R3: (0, B, C+2, D+3, B+C+2) → (2, B, C+1, D+3, B+C+1)
  rw [show C + 2 = (C + 1) + 1 from by ring,
      show B + (C + 2) = (B + C + 1) + 1 from by ring]
  step fm  -- R3
  finish

-- R1R1R3 rounds by induction
theorem r1r1r3_rounds : ∀ k, ∀ C D, ⟨2, B+2*k, C, D+1, B+C+2*k⟩ [fm]⊢* ⟨2, B, C+k, D+1+2*k, B+C+k⟩ := by
  intro k; induction' k with k h <;> intro C D
  · exists 0
  have h1 : ⟨2, B+2*k+2, C, D+1, B+C+2*k+2⟩ [fm]⊢⁺ ⟨2, B+2*k, C+1, D+3, B+C+2*k+1⟩ := by
    have := @r1r1r3_one (B + 2 * k) C D
    rw [show B + 2 * k + 2 = B + 2 * k + 2 from rfl,
        show B + 2 * k + C + 2 = B + C + 2 * k + 2 from by ring,
        show B + 2 * k + C + 1 = B + C + 2 * k + 1 from by ring] at this
    exact this
  rw [show B + 2 * (k + 1) = B + 2 * k + 2 from by ring,
      show B + C + 2 * (k + 1) = B + C + 2 * k + 2 from by ring]
  apply stepStar_trans (stepPlus_stepStar h1)
  rw [show B + C + 2 * k + 1 = B + (C + 1) + 2 * k from by ring]
  have h2 := h (C + 1) (D + 2)
  rw [show D + 3 = (D + 2) + 1 from by ring]
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- Phase 4 for even b: (2, 2K, 0, 1, 2K) →* (0, 0, K+1, 2K+1, K+1)
-- then r3r2r2 chain to (0, 0, 0, 2K+1, 2K+2)
theorem phase4_even (K : ℕ) : ⟨2, 2*K, 0, 1, 2*K⟩ [fm]⊢* ⟨0, 0, 0, 2*K+1, 2*K+2⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 0, K, 1 + 2 * K, K⟩)
  · have h := @r1r1r3_rounds 0 K 0 0
    simp only [Nat.zero_add, Nat.add_zero] at h; exact h
  -- Now (2, 0, K, 1+2K, K): a=2, b=0, so R2 fires
  -- R2: (2, 0, K, 1+2K, K) → (1, 0, K, 1+2K, K+1)
  -- R2: (1, 0, K, 1+2K, K+1) → (0, 0, K, 1+2K, K+2)
  -- Then r3r2r2 chain for K rounds: (0, 0, K, 1+2K, K+2) → but wait, we need form (0, 0, c+k, D, e+k)
  -- Actually: (0, 0, 0+K, 2K+1, 2+K) with k=K, c=0, e=2: (0, 0, 0, 2K+1, 2+2K)
  -- Hmm but r3r2r2_chain needs e >= 1 which means e+k >= k so e=2 >= 1 for first round. OK.
  -- But when K=0: (2, 0, 0, 1, 0) → R2: (1, 0, 0, 1, 1) → R2: (0, 0, 0, 1, 2). Done!
  rcases K with _ | K
  · -- K=0: (2, 0, 0, 1, 0)
    execute fm 2
  · -- K+1: (2, 0, K+1, 1+2*(K+1), K+1)
    step fm  -- R2
    step fm  -- R2
    -- Now: (0, 0, K+1, 1+2*(K+1), K+1+1+1)
    rw [show K + 1 + 1 + 1 = 2 + (K + 1) from by ring,
        show 1 + 2 * (K + 1) = 2 * K + 3 from by ring]
    have h := @r3r2r2_chain (2 * K + 3) (K + 1) 0 2
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish

-- Phase 4 for odd b: (2, 2K+1, 0, 1, 2K+1) →* (0, 0, 0, 2K+2, 2K+3)
theorem phase4_odd (K : ℕ) : ⟨2, 2*K+1, 0, 1, 2*K+1⟩ [fm]⊢* ⟨0, 0, 0, 2*K+2, 2*K+3⟩ := by
  -- r1r1r3_rounds with B=1, K rounds
  apply stepStar_trans (c₂ := ⟨2, 1, K, 1 + 2 * K, K + 1⟩)
  · have h := @r1r1r3_rounds 1 K 0 0
    simp only [Nat.zero_add, Nat.add_zero] at h
    rw [show 2 * K + 1 = 1 + 2 * K from by ring]
    simp only [Nat.add_comm 1 K] at h; exact h
  -- (2, 1, K, 1+2K, K+1)
  -- R1: a=2>=1, b=1>=1 → (1, 0, K+1, 2+2K, K+1)
  apply stepStar_trans (c₂ := ⟨1, 0, K + 1, 2 + 2 * K, K + 1⟩)
  · have : ⟨2, 1, K, 1 + 2 * K, K + 1⟩ [fm]⊢ ⟨1, 0, K + 1, 1 + 2 * K + 1, K + 1⟩ := by
      show fm ⟨1 + 1, 0 + 1, K, 1 + 2 * K, K + 1⟩ = some ⟨1, 0, K + 1, 1 + 2 * K + 1, K + 1⟩
      simp [fm]
    rw [show 1 + 2 * K + 1 = 2 + 2 * K from by ring] at this
    exact step_stepStar this
  -- (1, 0, K+1, 2+2K, K+1): a=1>=1, b=0, so R2 fires
  -- R2: (0, 0, K+1, 2+2K, K+2)
  -- Then R3R2R2 chain for K+1 rounds
  -- (0, 0, 0+(K+1), 2+2K, e+(K+1)) where e = 1: (0, 0, K+1, 2+2K, K+2)
  -- Result: (0, 0, 0, 2+2K, 1+2*(K+1)) = (0, 0, 0, 2K+2, 2K+3) ✓
  step fm  -- R2: (1, 0, K+1, 2+2K, K+1) → (0, 0, K+1, 2+2K, K+2)
  rw [show K + 1 + 1 = 1 + (K + 1) from by ring]
  have h := @r3r2r2_chain (2 + 2 * K) (K + 1) 0 1
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition: (0, 0, 0, d, d+1) ⊢⁺ (0, 0, 0, d+1, d+2)
theorem main_trans : ⟨0, 0, 0, d, d+1⟩ [fm]⊢⁺ ⟨0, 0, 0, d+1, d+2⟩ := by
  -- Phase 1: R4 repeated d times: (0, 0, 0, d, d+1) →* (0, d, 0, 0, d+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, d, 0, 0, d+1⟩)
  · have h := @d_to_b (b := 0) (k := d) (d := 0) (e := d + 1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step: (0, d, 0, 0, d+1) → (2, d, 0, 1, d)
  apply step_stepStar_stepPlus (c₂ := ⟨2, d, 0, 1, d⟩)
  · show fm ⟨0, d, 0, 0, d + 1⟩ = some ⟨2, d, 0, 1, d⟩; simp [fm]
  -- Phase 3+4: (2, d, 0, 1, d) →* (0, 0, 0, d+1, d+2)
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    refine stepStar_trans (phase4_even K) ?_; ring_nf; finish
  · subst hK
    refine stepStar_trans (phase4_odd K) ?_; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨0, 0, 0, d+1, d+2⟩) 0
  intro d; exact ⟨d+1, main_trans⟩
