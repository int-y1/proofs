import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #41: [35/6, 4/55, 11/2, 3/7, 70/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 1  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_41

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d+1, e⟩
  | _ => none

-- R3 repeated: a → e
theorem a_to_e : ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+k⟩ := by
  have many_step : ∀ k a e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a e

-- R4 repeated: d → b
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- R2 repeated: c,e → a
theorem r2_chain : ⟨a, 0, c+k, d, k⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0⟩ := by
  have many_step : ∀ k a c, ⟨a, 0, c+k, d, k⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a c
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a c

-- R1R1R2 single round
theorem r1r1r2_one : ⟨2, B+2, C, D, E+1⟩ [fm]⊢⁺ ⟨2, B, C+1, D+2, E⟩ := by
  rw [show B + 2 = (B + 1) + 1 from by ring]
  step fm
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring,
      show E + 1 = E + 1 from rfl]
  step fm
  finish

-- R1R1R2 rounds
theorem r1r1r2_rounds : ∀ k, ∀ C D E, ⟨2, B+2*k, C, D, E+k⟩ [fm]⊢* ⟨2, B, C+k, D+2*k, E⟩ := by
  intro k; induction' k with k h <;> intro C D E
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  have h1 := @r1r1r2_one (B + 2 * k) C D (E + k)
  apply stepStar_trans (stepPlus_stepStar h1)
  have h2 := h (C + 1) (D + 2) E
  refine stepStar_trans h2 ?_
  ring_nf; finish

-- Phase 4 even: d' = 2K
theorem phase4_even (K : ℕ) : ⟨2, 2*K, 1, 2, 2*K⟩ [fm]⊢* ⟨2+2*K, 0, 1, 2+2*K, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 0, 1+K, 2+2*K, K⟩)
  · have h := @r1r1r2_rounds 0 K 1 2 K
    rw [show 0 + 2 * K = 2 * K from by ring,
        show K + K = 2 * K from by ring] at h
    exact h
  have h := @r2_chain 2 1 K (2 + 2 * K)
  rw [show 1 + K = 1 + K from rfl] at h
  exact h

-- Phase 4 odd: d' = 2K+1
theorem phase4_odd (K : ℕ) : ⟨2, 2*K+1, 1, 2, 2*K+1⟩ [fm]⊢* ⟨2*K+3, 0, 1, 2*K+3, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 1, 1+K, 2+2*K, K+1⟩)
  · have h := @r1r1r2_rounds 1 K 1 2 (K+1)
    rw [show 1 + 2 * K = 2 * K + 1 from by ring,
        show K + 1 + K = 2 * K + 1 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨1, 0, 1+K+1, 2+2*K+1, K+1⟩)
  · have : ⟨2, 1, 1+K, 2+2*K, K+1⟩ [fm]⊢ ⟨1, 0, 1+K+1, 2+2*K+1, K+1⟩ := by
      show fm ⟨1+1, 0+1, 1+K, 2+2*K, K+1⟩ = some ⟨1, 0, 1+K+1, 2+2*K+1, K+1⟩
      simp [fm]
    exact step_stepStar this
  have h := @r2_chain 1 1 (K+1) (2 + 2 * K + 1)
  rw [show 1 + (K + 1) = 1 + K + 1 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Tail step
theorem tail_step (N D : ℕ) : ⟨N+1, 0, 1, D, 0⟩ [fm]⊢⁺ ⟨N+2, 0, 0, D, 0⟩ := by
  step fm
  step fm
  finish

-- Main transition
theorem main_trans : ⟨d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨d+2, 0, 0, d+1, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, d, 0, 0, d+1⟩)
  · apply stepStar_trans (c₂ := ⟨0, 0, 0, d, d+1⟩)
    · have h := @a_to_e 0 (d + 1) d 0
      simp only [Nat.zero_add] at h; exact h
    · have h := @d_to_b 0 0 d (d + 1)
      simp only [Nat.zero_add] at h; exact h
  -- R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨1, d, 1, 1, d⟩)
  · show fm ⟨0, d, 0, 0, d + 1⟩ = some ⟨1, d, 1, 1, d⟩; simp [fm]
  rcases d with _ | d'
  · execute fm 2
  · apply stepStar_trans (c₂ := ⟨2, d', 1, 2, d'⟩)
    · apply stepStar_trans (c₂ := ⟨0, d', 2, 2, d' + 1⟩)
      · have : ⟨1, d' + 1, 1, 1, d' + 1⟩ [fm]⊢ ⟨0, d', 2, 2, d' + 1⟩ := by
          show fm ⟨0 + 1, d' + 1, 1, 1, d' + 1⟩ = some ⟨0, d', 2, 2, d' + 1⟩
          simp [fm]
        exact step_stepStar this
      · have : ⟨0, d', 2, 2, d' + 1⟩ [fm]⊢ ⟨2, d', 1, 2, d'⟩ := by
          show fm ⟨0, d', 1 + 1, 2, d' + 1⟩ = some ⟨2, d', 1, 2, d'⟩
          simp [fm]
        exact step_stepStar this
    -- Parity split on d'
    rcases Nat.even_or_odd d' with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      apply stepStar_trans (phase4_even K)
      have h := @tail_step (1 + 2 * K) (2 + 2 * K)
      rw [show 1 + 2 * K + 1 = 2 + 2 * K from by ring] at h
      refine stepPlus_stepStar ?_
      rw [show 2 * K + 1 + 2 = 1 + 2 * K + 2 from by ring,
          show 2 * K + 1 + 1 = 2 + 2 * K from by ring]
      exact h
    · subst hK
      apply stepStar_trans (phase4_odd K)
      have h := @tail_step (2 * K + 2) (2 * K + 3)
      rw [show 2 * K + 2 + 1 = 2 * K + 3 from by ring] at h
      refine stepPlus_stepStar ?_
      rw [show 2 * K + 1 + 1 + 2 = 2 * K + 2 + 2 from by ring,
          show 2 * K + 1 + 1 + 1 = 2 * K + 3 from by ring]
      exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨d+2, 0, 0, d+1, 0⟩) 0
  intro d
  exact ⟨d+1, by
    have := @main_trans (d+1)
    rw [show d + 1 + 1 = d + 2 from by ring,
        show d + 1 + 2 = d + 3 from by ring] at this
    exact this⟩
