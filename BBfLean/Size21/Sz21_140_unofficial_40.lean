import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #40: [35/6, 4/55, 11/2, 3/7, 28/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_40

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
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

-- One R1R1R2 round: 3 steps
theorem r1r1r2_one : ⟨2, B+2, C, D+1, B+C+2⟩ [fm]⊢⁺ ⟨2, B, C+1, D+3, B+C+1⟩ := by
  rw [show B + 2 = (B + 1) + 1 from by ring]
  step fm
  rw [show B + C + 2 = B + (C + 2) from by ring]
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring,
      show B + (C + 2) = (B + C + 1) + 1 from by ring]
  step fm
  finish

-- R1R1R2 rounds by induction
theorem r1r1r2_rounds : ∀ k, ∀ C D, ⟨2, B+2*k, C, D+1, B+C+2*k⟩ [fm]⊢* ⟨2, B, C+k, D+1+2*k, B+C+k⟩ := by
  intro k; induction' k with k h <;> intro C D
  · exists 0
  -- Establish the 3-step round
  have h1 : ⟨2, B+2*k+2, C, D+1, B+C+2*k+2⟩ [fm]⊢⁺ ⟨2, B+2*k, C+1, D+3, B+C+2*k+1⟩ := by
    have := @r1r1r2_one (B + 2 * k) C D
    rw [show B + 2 * k + 2 = B + 2 * k + 2 from rfl,
        show B + 2 * k + C + 2 = B + C + 2 * k + 2 from by ring,
        show B + 2 * k + C + 1 = B + C + 2 * k + 1 from by ring] at this
    exact this
  -- Rewrite goal LHS
  rw [show B + 2 * (k + 1) = B + 2 * k + 2 from by ring,
      show B + C + 2 * (k + 1) = B + C + 2 * k + 2 from by ring]
  apply stepStar_trans (stepPlus_stepStar h1)
  -- Apply IH
  rw [show B + C + 2 * k + 1 = B + (C + 1) + 2 * k from by ring]
  have h2 := h (C + 1) (D + 2)
  rw [show D + 3 = (D + 2) + 1 from by ring]
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- Phase 4 for even d
theorem phase4_even (K : ℕ) : ⟨2, 2*K, 0, 1, 2*K⟩ [fm]⊢* ⟨2+2*K, 0, 0, 1+2*K, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 0, K, 1 + 2 * K, K⟩)
  · have h := @r1r1r2_rounds 0 K 0 0
    simp only [Nat.zero_add, Nat.add_zero] at h; exact h
  · have h := @r2_chain 2 0 K (1 + 2 * K)
    simp only [Nat.zero_add] at h; exact h

-- Phase 4 for odd d
theorem phase4_odd (K : ℕ) : ⟨2, 2*K+1, 0, 1, 2*K+1⟩ [fm]⊢* ⟨2*K+3, 0, 0, 2*K+2, 0⟩ := by
  -- r1r1r2_rounds with B=1
  apply stepStar_trans (c₂ := ⟨2, 1, K, 1 + 2 * K, K + 1⟩)
  · have h := @r1r1r2_rounds 1 K 0 0
    simp only [Nat.zero_add, Nat.add_zero] at h
    rw [show 2 * K + 1 = 1 + 2 * K from by ring]
    simp only [Nat.add_comm 1 K] at h; exact h
  -- R1: (2, 1, K, 1+2K, K+1) → (1, 0, K+1, 2+2K, K+1)
  -- R1 matches: a+1=2 (a=1), b+1=1 (b=0) → (1, 0, K+1, (1+2K)+1, K+1)
  apply stepStar_trans (c₂ := ⟨1, 0, K + 1, 2 + 2 * K, K + 1⟩)
  · have : ⟨2, 1, K, 1 + 2 * K, K + 1⟩ [fm]⊢ ⟨1, 0, K + 1, 1 + 2 * K + 1, K + 1⟩ := by
      show fm ⟨1 + 1, 0 + 1, K, 1 + 2 * K, K + 1⟩ = some ⟨1, 0, K + 1, 1 + 2 * K + 1, K + 1⟩
      simp [fm]
    rw [show 1 + 2 * K + 1 = 2 + 2 * K from by ring] at this
    exact step_stepStar this
  -- r2_chain: (1, 0, 0+(K+1), 2+2K, K+1) →* (1+2*(K+1), 0, 0, 2+2K, 0)
  have h := @r2_chain 1 0 (K + 1) (2 + 2 * K)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition
theorem main_trans : ⟨d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨d+2, 0, 0, d+1, 0⟩ := by
  -- Phases 1+2: (d+1, 0, 0, d, 0) →* (0, d, 0, 0, d+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, d, 0, 0, d+1⟩)
  · apply stepStar_trans (c₂ := ⟨0, 0, 0, d, d+1⟩)
    · have h := @a_to_e 0 (d + 1) d 0
      simp only [Nat.zero_add] at h
      -- h : (d + 1, 0, 0, d, 0) →* (0, 0, 0, d, d + 1)
      exact h
    · have h := @d_to_b 0 0 d (d + 1)
      simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step (gives stepPlus)
  apply step_stepStar_stepPlus (c₂ := ⟨2, d, 0, 1, d⟩)
  · show fm ⟨0, d, 0, 0, d + 1⟩ = some ⟨2, d, 0, 1, d⟩; simp [fm]
  -- Phase 4
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    refine stepStar_trans (phase4_even K) ?_; ring_nf; finish
  · subst hK
    refine stepStar_trans (phase4_odd K) ?_; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨d+1, 0, 0, d, 0⟩) 0
  intro d; exact ⟨d+1, main_trans⟩
