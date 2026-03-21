import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #44: [35/6, 4/55, 121/2, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_44

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R3 repeated: a → e+2 (when b=0, c=0)
theorem a_to_e : ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  have many_step : ∀ k a e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
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
theorem r2_chain : ∀ k, ∀ a c, ⟨a, 0, c+k, d, F+k⟩ [fm]⊢* ⟨a+2*k, 0, c, d, F⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show F + (k + 1) = (F + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- One R1R1R2 round: 3 steps
theorem r1r1r2_one : ⟨2, B+2, C, D+1, E+1⟩ [fm]⊢⁺ ⟨2, B, C+1, D+3, E⟩ := by
  rw [show B + 2 = (B + 1) + 1 from by ring]
  step fm
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  finish

-- R1R1R2 rounds by induction
theorem r1r1r2_rounds : ∀ k, ∀ C D E, ⟨2, B+2*k, C, D+1, E+k⟩ [fm]⊢* ⟨2, B, C+k, D+1+2*k, E⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · exists 0
  rw [show B + 2 * (k + 1) = B + 2 * k + 2 from by ring,
      show E + (k + 1) = E + k + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (@r1r1r2_one (B + 2 * k) C D (E + k)))
  have h2 := ih (C + 1) (D + 2) E
  rw [show D + 3 = (D + 2) + 1 from by ring]
  refine stepStar_trans h2 ?_
  rw [show C + 1 + k = C + (k + 1) from by ring,
      show D + 2 + 1 + 2 * k = D + 1 + 2 * (k + 1) from by ring]
  exists 0

-- Phase 5 for even d=2K
theorem phase5_even (K e : ℕ) :
    ⟨2, 2*K, 0, 1, e + 2*(2*K)⟩ [fm]⊢* ⟨2+2*K, 0, 0, 1+2*K, e+2*K⟩ := by
  apply stepStar_trans (c₂ := ⟨2, 0, K, 1 + 2 * K, e + 3 * K⟩)
  · -- r1r1r2_rounds with B=0, k=K
    have h := @r1r1r2_rounds 0 K 0 0 (e + 3 * K)
    show ∃ n, (2, 2 * K, 0, 1, e + 2 * (2 * K)) [fm]⊢^{n} (2, 0, K, 1 + 2 * K, e + 3 * K)
    rw [show (0 : ℕ) + 2 * K = 2 * K from by ring,
        show (0 : ℕ) + 1 = 1 from by ring,
        show (e + 3 * K) + K = e + 2 * (2 * K) from by ring,
        show (0 : ℕ) + K = K from by ring,
        show (0 : ℕ) + 1 + 2 * K = 1 + 2 * K from by ring] at h
    exact h
  · -- r2_chain with F=e+2*K, k=K, a=2, c=0, d=1+2*K
    have h := @r2_chain (1 + 2 * K) (e + 2 * K) K 2 0
    show ∃ n, (2, 0, K, 1 + 2 * K, e + 3 * K) [fm]⊢^{n} (2 + 2 * K, 0, 0, 1 + 2 * K, e + 2 * K)
    rw [show (e + 2 * K) + K = e + 3 * K from by ring,
        show (0 : ℕ) + K = K from by ring,
        show 2 + 2 * K = 2 + 2 * K from rfl] at h
    exact h

-- Phase 5 for odd d=2K+1
theorem phase5_odd (K e : ℕ) :
    ⟨2, 2*K+1, 0, 1, e + 2*(2*K+1)⟩ [fm]⊢* ⟨2*K+3, 0, 0, 2*K+2, e+2*K+1⟩ := by
  -- K rounds with B=1
  apply stepStar_trans (c₂ := ⟨2, 1, K, 2 * K + 1, e + 3 * K + 2⟩)
  · have h := @r1r1r2_rounds 1 K 0 0 (e + 3 * K + 2)
    simp only [Nat.zero_add] at h
    rw [show (e + 3 * K + 2) + K = e + 2 * (2 * K + 1) from by ring,
        show (1 : ℕ) + 2 * K = 2 * K + 1 from by ring] at h
    exact h
  -- R1: (2, 1, K, 2K+1, e+3K+2) → (1, 0, K+1, 2K+2, e+3K+2)
  apply stepStar_trans (c₂ := ⟨1, 0, K + 1, 2 * K + 2, e + 3 * K + 2⟩)
  · have : fm ⟨1 + 1, 0 + 1, K, 2 * K + 1, e + 3 * K + 2⟩ =
           some ⟨1, 0, K + 1, 2 * K + 1 + 1, e + 3 * K + 2⟩ := by simp [fm]
    rw [show (1 : ℕ) + 1 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl,
        show 2 * K + 1 + 1 = 2 * K + 2 from by ring] at this
    exact step_stepStar this
  -- R2 chain with F=e+2*K+1, k=K+1
  have h := @r2_chain (2 * K + 2) (e + 2 * K + 1) (K + 1) 1 0
  rw [show (e + 2 * K + 1) + (K + 1) = e + 3 * K + 2 from by ring,
      show (0 : ℕ) + (K + 1) = K + 1 from by ring,
      show 1 + 2 * (K + 1) = 2 * K + 3 from by ring] at h
  exact h

-- Main transition
theorem main_trans (d e : ℕ) : ⟨d+1, 0, 0, d, e⟩ [fm]⊢⁺ ⟨d+2, 0, 0, d+1, e+d⟩ := by
  -- Phase 1+2: (d+1, 0, 0, d, e) →* (0, d, 0, 0, e+2*(d+1))
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, d, 0, 0, e + 2*(d+1)⟩)
  · apply stepStar_trans (c₂ := ⟨0, 0, 0, d, e + 2*(d+1)⟩)
    · have h := @a_to_e 0 (d + 1) d e; simp only [Nat.zero_add] at h; exact h
    · have h := @d_to_b 0 0 d (e + 2*(d+1)); simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 step
  apply step_stepPlus_stepPlus (c₂ := ⟨0, d, 1, 1, e + 2*d + 1⟩)
  · show fm ⟨0, d, 0, 0, e + 2 * (d + 1)⟩ = some ⟨0, d, 1, 1, e + 2 * d + 1⟩
    rw [show e + 2 * (d + 1) = (e + 2 * d + 1) + 1 from by ring]; simp [fm]
  -- Phase 4: R2 step + Phase 5
  apply step_stepStar_stepPlus (c₂ := ⟨2, d, 0, 1, e + 2*d⟩)
  · show fm ⟨0, d, 0 + 1, 1, (e + 2 * d) + 1⟩ = some ⟨0 + 2, d, 0, 1, e + 2 * d⟩
    rw [show e + 2 * d + 1 = (e + 2 * d) + 1 from by ring]; simp [fm]
  -- Phase 5
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · rw [show K + K = 2 * K from by ring] at hK; subst hK
    -- goal: (2, 2*K, 0, 1, e+2*(2*K)) ⊢* (2*K+2, 0, 0, 2*K+1, e+2*K)
    -- phase5_even: (2, 2*K, 0, 1, e+2*(2*K)) ⊢* (2+2*K, 0, 0, 1+2*K, e+2*K)
    rw [show 2 * K + 2 = 2 + 2 * K from by ring,
        show 2 * K + 1 = 1 + 2 * K from by ring]
    exact phase5_even K e
  · subst hK
    -- goal: (2, 2*K+1, 0, 1, e+2*(2*K+1)) ⊢* (2*K+3, 0, 0, 2*K+2, e+2*K+1)
    exact phase5_odd K e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ) (fun ⟨d, e⟩ ↦ ⟨d+1, 0, 0, d, e⟩) ⟨0, 0⟩
  intro ⟨d, e⟩; exact ⟨⟨d+1, e+d⟩, main_trans d e⟩
