import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #39: [35/6, 4/55, 11/2, 3/7, 12/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 2  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_39

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

-- R3 repeated: a → e (when b=0, c=0)
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

-- R2 repeated: c,e → a (when b=0)
theorem r2_chain : ⟨a, 0, c+k, d, k⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0⟩ := by
  have many_step : ∀ k a c, ⟨a, 0, c+k, d, k⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a c
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a c

-- R1R1R2 rounds: from (2, B+2k, C, D, E+k) →* (2, B, C+k, D+2k, E)
theorem r1r1r2_rounds : ∀ k, ∀ B C D E, ⟨2, B+2*k, C, D, E+k⟩ [fm]⊢* ⟨2, B, C+k, D+2*k, E⟩ := by
  intro k; induction' k with k h <;> intro B C D E
  · exists 0
  have step1 : ⟨2, B + 2*k + 2, C, D, E + k + 1⟩ [fm]⊢* ⟨2, B, C + k + 1, D + 2*k + 2, E⟩ := by
    rw [show B + 2 * k + 2 = (B + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show B + 2 * k + 1 = (B + 2 * k) + 1 from by ring]
    step fm
    rw [show C + 1 + 1 = (C + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (h B (C+1) (D+2) E)
    ring_nf; finish
  convert step1 using 2

-- R3 + R2 cleanup: (a+1, 0, 1, d, 0) →* (a+2, 0, 0, d, 0)
theorem r3_r2_cleanup : ⟨a+1, 0, 1, d, 0⟩ [fm]⊢* ⟨a+2, 0, 0, d, 0⟩ := by
  step fm
  rw [show (1 : ℕ) = 0 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  ring_nf; finish

-- Phase 4 for even d: d = 2K
-- (2, 2K+1, 0, 0, 2K) →* (2K+2, 0, 0, 2K+1, 0)
theorem phase4_even (K : ℕ) : ⟨2, 2*K+1, 0, 0, 2*K⟩ [fm]⊢* ⟨2*K+2, 0, 0, 2*K+1, 0⟩ := by
  -- K R1R1R2 rounds: →* (2, 1, K, 2K, K)
  apply stepStar_trans (c₂ := ⟨2, 1, K, 2*K, K⟩)
  · have h := r1r1r2_rounds K 1 0 0 K
    convert h using 2; ring_nf
  -- R1: (2, 1, K, 2K, K) → (1, 0, K+1, 2K+1, K)
  apply stepStar_trans (c₂ := ⟨1, 0, K+1, 2*K+1, K⟩)
  · rw [show (2 : ℕ) = 1 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
    step fm; finish
  -- K R2s: (1, 0, 1+K, 2K+1, K) →* (1+2K, 0, 1, 2K+1, 0)
  apply stepStar_trans (c₂ := ⟨1+2*K, 0, 1, 2*K+1, 0⟩)
  · have h := @r2_chain (1) (1) K (2*K+1)
    convert h using 2; ring_nf
  -- R3 + R2: (1+2K, 0, 1, 2K+1, 0) → (2K+2, 0, 0, 2K+1, 0)
  have h := @r3_r2_cleanup (2*K) (2*K+1)
  convert h using 2; ring_nf

-- Phase 4 for odd d: d = 2K+1
-- (2, 2K+2, 0, 0, 2K+1) →* (2K+3, 0, 0, 2K+2, 0)
theorem phase4_odd (K : ℕ) : ⟨2, 2*K+2, 0, 0, 2*K+1⟩ [fm]⊢* ⟨2*K+3, 0, 0, 2*K+2, 0⟩ := by
  -- K R1R1R2 rounds: →* (2, 2, K, 2K, K+1)
  apply stepStar_trans (c₂ := ⟨2, 2, K, 2*K, K+1⟩)
  · have h := r1r1r2_rounds K 2 0 0 (K+1)
    convert h using 2; ring_nf
  -- 2 R1 steps: (2, 2, K, 2K, K+1) →* (0, 0, K+2, 2K+2, K+1)
  apply stepStar_trans (c₂ := ⟨0, 0, K+2, 2*K+2, K+1⟩)
  · have h1 : ⟨2, 2, K, 2*K, K+1⟩ [fm]⊢ ⟨1, 1, K+1, 2*K+1, K+1⟩ := by
      show fm ⟨1+1, 1+1, K, 2*K, K+1⟩ = some ⟨1, 1, K+1, 2*K+1, K+1⟩; simp [fm]
    have h2 : ⟨1, 1, K+1, 2*K+1, K+1⟩ [fm]⊢ ⟨0, 0, K+2, 2*K+2, K+1⟩ := by
      show fm ⟨0+1, 0+1, K+1, 2*K+1, K+1⟩ = some ⟨0, 0, K+2, 2*K+2, K+1⟩; simp [fm]
    exact stepStar_trans (step_stepStar h1) (step_stepStar h2)
  -- (K+1) R2s: (0, 0, 1+(K+1), 2K+2, K+1) →* (2(K+1), 0, 1, 2K+2, 0)
  apply stepStar_trans (c₂ := ⟨2*(K+1), 0, 1, 2*K+2, 0⟩)
  · have h := @r2_chain (0) (1) (K+1) (2*K+2)
    convert h using 2; ring_nf
  -- R3 + R2: (2(K+1), 0, 1, 2K+2, 0) → (2K+3, 0, 0, 2K+2, 0)
  have h := @r3_r2_cleanup (2*K+1) (2*K+2)
  convert h using 2

-- Main transition: (d+1, 0, 0, d, 0) ⊢⁺ (d+2, 0, 0, d+1, 0)
theorem main_trans : ⟨d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨d+2, 0, 0, d+1, 0⟩ := by
  -- Phase 1: R3 repeated: (d+1, 0, 0, d, 0) →* (0, 0, 0, d, d+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, d, d+1⟩)
  · have h := @a_to_e 0 (d+1) d 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 repeated: (0, 0, 0, d, d+1) →* (0, d, 0, 0, d+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, d, 0, 0, d+1⟩)
  · have h := @d_to_b 0 0 d (d+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step: (0, d, 0, 0, d+1) → (2, d+1, 0, 0, d)
  apply step_stepStar_stepPlus (c₂ := ⟨2, d+1, 0, 0, d⟩)
  · show fm ⟨0, d, 0, 0, d + 1⟩ = some ⟨2, d + 1, 0, 0, d⟩; simp [fm]
  -- Phase 4: parity case split on d
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- d = 2K (even)
    rw [show K + K = 2 * K from by ring] at hK; subst hK
    refine stepStar_trans (phase4_even K) ?_; ring_nf; finish
  · -- d = 2K + 1 (odd)
    subst hK
    refine stepStar_trans (phase4_odd K) ?_; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨d+1, 0, 0, d, 0⟩) 1
  intro d; exact ⟨d+1, main_trans⟩
