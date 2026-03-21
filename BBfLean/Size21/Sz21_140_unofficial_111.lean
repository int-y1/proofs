import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #111: [77/15, 2/3, 9/14, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  0  0
-1  2  0 -1  0
 0  0  1  0 -1
-1  1  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_111

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

-- R4 repeated: e→c (b=0, d=0, a≥1)
theorem e_to_c : ⟨a+1, 0, c, 0, e+k⟩ [fm]⊢* ⟨a+1, 0, c+k, 0, e⟩ := by
  have many_step : ∀ k c e, ⟨a+1, 0, c, 0, e+k⟩ [fm]⊢* ⟨a+1, 0, c+k, 0, e⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- R2 repeated: b→a
theorem b_to_a : ⟨a, b+k, 0, d, e⟩ [fm]⊢* ⟨a+k, b, 0, d, e⟩ := by
  have many_step : ∀ k a b, ⟨a, b+k, 0, d, e⟩ [fm]⊢* ⟨a+k, b, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro a b
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a b

-- R3/R2/R2 chain
theorem r3r2r2_chain : ∀ k, ∀ a d, ⟨a+1, 0, 0, d+k, e⟩ [fm]⊢* ⟨a+1+k, 0, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1,R1,R3 chain: k rounds
theorem r1r1r3_chain : ∀ k, ∀ A C D E, ⟨A+k, 2, C+2*k, D, E⟩ [fm]⊢* ⟨A, 2, C, D+k, E+2*k⟩ := by
  intro k; induction' k with k h <;> intro A C D E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Phase 3 for odd e=2m+1: (2m+1, 1, 2m+1, 1, 1) ⊢* (m, 2, 0, m+1, 2m+2)
theorem phase3_odd (m : ℕ) : ⟨2*m+1, 1, 2*m+1, 1, 1⟩ [fm]⊢* ⟨m, 2, 0, m+1, 2*m+2⟩ := by
  apply stepStar_trans (c₂ := ⟨2 * m + 1, 0, 2 * m, 2, 2⟩)
  · have : fm ⟨2 * m + 1, 0 + 1, (2 * m) + 1, 1, 1⟩ = some ⟨2 * m + 1, 0, 2 * m, 2, 2⟩ := by
      simp [fm]
    rw [show (2 * m) + 1 = 2 * m + 1 from by ring] at this
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨2 * m, 2, 2 * m, 1, 2⟩)
  · rw [show 2 * m + 1 = (2 * m) + 1 from by ring]
    have : fm ⟨(2 * m) + 1, 0, 2 * m, 1 + 1, 2⟩ = some ⟨2 * m, 0 + 2, 2 * m, 1, 2⟩ := by
      simp [fm]
    exact step_stepStar this
  have h := @r1r1r3_chain m m 0 1 2
  rw [show m + m = 2 * m from by ring, show 0 + 2 * m = 2 * m from by ring] at h
  refine stepStar_trans h ?_; ring_nf; finish

-- Phase 3 for even e=2(K+1): (2K+2, 1, 2K+2, 1, 1) ⊢* (K+1, 1, 0, K+2, 2K+3)
-- R1: (2K+2, 0, 2K+1, 2, 2)
-- R3: (2K+1, 2, 2K+1, 1, 2)
-- K rounds of r1r1r3: (K+1, 2, 1, K+1, 2K+2)
-- R1: (K+1, 1, 0, K+2, 2K+3)
theorem phase3_even (K : ℕ) : ⟨2*K+2, 1, 2*K+2, 1, 1⟩ [fm]⊢* ⟨K+1, 1, 0, K+2, 2*K+3⟩ := by
  apply stepStar_trans (c₂ := ⟨2 * K + 2, 0, 2 * K + 1, 2, 2⟩)
  · have : fm ⟨2 * K + 2, 0 + 1, (2 * K + 1) + 1, 1, 1⟩ = some ⟨2 * K + 2, 0, 2 * K + 1, 2, 2⟩ := by
      simp [fm]
    rw [show (2 * K + 1) + 1 = 2 * K + 2 from by ring] at this
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨2 * K + 1, 2, 2 * K + 1, 1, 2⟩)
  · rw [show 2 * K + 2 = (2 * K + 1) + 1 from by ring]
    have : fm ⟨(2 * K + 1) + 1, 0, 2 * K + 1, 1 + 1, 2⟩ = some ⟨2 * K + 1, 0 + 2, 2 * K + 1, 1, 2⟩ := by
      simp [fm]
    exact step_stepStar this
  -- K rounds: (2K+1, 2, 2K+1, 1, 2) -> (K+1, 2, 1, K+1, 2K+2)
  apply stepStar_trans (c₂ := ⟨K + 1, 2, 1, K + 1, 2 * K + 2⟩)
  · have h := @r1r1r3_chain K (K + 1) 1 1 2
    rw [show (K + 1) + K = 2 * K + 1 from by ring,
        show 1 + 2 * K = 2 * K + 1 from by ring,
        show 1 + K = K + 1 from by ring,
        show 2 + 2 * K = 2 * K + 2 from by ring] at h
    exact h
  -- Final R1: (K+1, 2, 1, K+1, 2K+2) -> (K+1, 1, 0, K+2, 2K+3)
  have : fm ⟨K + 1, 1 + 1, 0 + 1, K + 1, 2 * K + 2⟩ = some ⟨K + 1, 1, 0, (K + 1) + 1, (2 * K + 2) + 1⟩ := by
    simp [fm]
  rw [show (K + 1) + 1 = K + 2 from by ring,
      show (2 * K + 2) + 1 = 2 * K + 3 from by ring] at this
  exact step_stepStar this

-- Main transition: (e+1, 0, 0, 0, e) ⊢⁺ (e+2, 0, 0, 0, e+1)
theorem main_trans : ⟨e+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨e+2, 0, 0, 0, e+1⟩ := by
  -- Phase 1: (e+1, 0, 0, 0, e) -> (e+1, 0, e, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨e + 1, 0, e, 0, 0⟩)
  · have h := @e_to_c e 0 0 e
    rw [show 0 + e = e from by ring] at h; exact h
  -- Phase 2 R5: (e+1, 0, e, 0, 0) -> (e, 1, e, 1, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨e, 1, e, 1, 1⟩)
  · show fm ⟨e + 1, 0, e, 0, 0⟩ = some ⟨e, 1, e, 1, 1⟩; simp [fm]
  -- Split on parity
  rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    rcases K with _ | K
    · -- e=0: (0, 1, 0, 1, 1) ⊢* (2, 0, 0, 0, 1)
      execute fm 4
    -- e=2(K+1)=2K+2
    -- Phase 3: (2K+2, 1, 2K+2, 1, 1) ⊢* (K+1, 1, 0, K+2, 2K+3)
    -- phase3_even K : exactly this
    apply stepStar_trans (c₂ := ⟨K + 1, 1, 0, K + 2, 2 * K + 3⟩)
    · exact phase3_even K
    -- R2: (K+1, 1, 0, K+2, 2K+3) -> (K+2, 0, 0, K+2, 2K+3)
    apply stepStar_trans (c₂ := ⟨K + 2, 0, 0, K + 2, 2 * K + 3⟩)
    · have h := @b_to_a (K + 1) 0 1 (K + 2) (2 * K + 3)
      rw [show 0 + 1 = 1 from by ring, show K + 1 + 1 = K + 2 from by ring] at h; exact h
    -- R3/R2/R2 chain: (K+2, 0, 0, K+2, 2K+3) -> (2K+4, 0, 0, 0, 2K+3)
    -- r3r2r2_chain with a+1=K+2 (a=K+1), d=0, k=K+2
    have h := @r3r2r2_chain (2 * K + 3) (K + 1) K 0  -- wait let me compute
    -- r3r2r2_chain k a d: (a+1, 0, 0, d+k, e) ⊢* (a+1+k, 0, 0, d, e)
    -- We need: (K+2, 0, 0, K+2, 2K+3) ⊢* (2K+4, 0, 0, 0, 2K+3)
    -- So a+1 = K+2, d = 0, k = K+2: a = K+1
    -- (K+1+1, 0, 0, 0+(K+2), 2K+3) ⊢* (K+1+1+(K+2), 0, 0, 0, 2K+3)
    -- = (K+2, 0, 0, K+2, 2K+3) ⊢* (2K+4, 0, 0, 0, 2K+3) ✓
    have h := @r3r2r2_chain (2 * K + 3) (K + 2) (K + 1) 0
    rw [show 0 + (K + 2) = K + 2 from by ring] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · subst hK
    -- e=2K+1
    -- Phase 3: (2K+1, 1, 2K+1, 1, 1) ⊢* (K, 2, 0, K+1, 2K+2)
    apply stepStar_trans (c₂ := ⟨K, 2, 0, K + 1, 2 * K + 2⟩)
    · exact phase3_odd K
    -- R2,R2: (K, 2, 0, K+1, 2K+2) -> (K+2, 0, 0, K+1, 2K+2)
    apply stepStar_trans (c₂ := ⟨K + 2, 0, 0, K + 1, 2 * K + 2⟩)
    · have h := @b_to_a K 0 2 (K + 1) (2 * K + 2)
      rw [show 0 + 2 = 2 from by ring] at h; exact h
    -- R3/R2/R2 chain: (K+2, 0, 0, K+1, 2K+2) -> (2K+3, 0, 0, 0, 2K+2)
    -- a+1 = K+2, so a = K+1. d = 0, k = K+1.
    have h := @r3r2r2_chain (2 * K + 2) (K + 1) (K + 1) 0
    rw [show 0 + (K + 1) = K + 1 from by ring] at h
    refine stepStar_trans h ?_
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨e+1, 0, 0, 0, e⟩) 0
  intro e; exact ⟨e+1, main_trans⟩
