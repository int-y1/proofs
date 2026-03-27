import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #546: [28/45, 231/2, 1/147, 15/11, 1/3]

Vector representation:
```
 2 -2 -1  1  0
-1  1  0  1  1
 0 -1  0 -2  0
 0  1  1  0 -1
 0 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_546

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | ⟨a, b+1, c, d+2, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- R4/R3 interleaving: k rounds of (R4, R3)
theorem r4r3_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + 2*k, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R1,R2,R2 chain: c rounds
theorem r1r2r2_chain : ∀ c, ∀ d e, ⟨0, 2, c, d, e⟩ [fm]⊢* ⟨0, 2, 0, d + 3*c, e + 2*c⟩ := by
  intro c; induction' c with c h <;> intro d e
  · exists 0
  rw [show (c + 1 : ℕ) = c + 1 from rfl]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Full even transition as ⊢⁺
-- (0, 0, 0, 2k, 2k+2) ->+ (0, 0, 0, 3k+2, 3k+4)
theorem even_trans : ⟨0, 0, 0, 2*k, 2*k + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*k + 2, 3*k + 4⟩ := by
  -- Phase 1a: k rounds of R4/R3
  have phase1a := r4r3_chain k 0 0 (k + 2)
  rw [Nat.zero_add, Nat.zero_add] at phase1a
  rw [show 2 * k + 2 = (k + 2) + k from by ring]
  apply stepStar_stepPlus_stepPlus phase1a
  -- At (0, 0, k, 0, k+2): R4 step (for ⊢⁺)
  rw [show k + 2 = (k + 1) + 1 from by ring]
  step fm
  -- At (0, 1, k+1, 0, k+1): R4 step (continues ⊢⁺ via stepPlus_stepStar)
  rw [show k + 1 = k + 1 from rfl]
  step fm
  -- Now at (0, 2, k+1+1, 0, k) which is (0, 2, k+2, 0, k)
  -- Need: (0, 2, k+1+1, 0, k) ->* (0, 0, 0, 3k+2, 3k+4)
  rw [show k + 1 + 1 = k + 2 from by ring]
  apply stepStar_trans (r1r2r2_chain (k + 2) 0 k)
  rw [show 0 + 3 * (k + 2) = (3 * k + 2) + 4 from by ring,
      show k + 2 * (k + 2) = 3 * k + 4 from by ring]
  step fm; step fm
  ring_nf; finish

-- Full odd transition as ⊢⁺
-- (0, 0, 0, 2k+1, 2k+3) ->+ (0, 0, 0, 3k+3, 3k+5)
theorem odd_trans : ⟨0, 0, 0, 2*k + 1, 2*k + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*k + 3, 3*k + 5⟩ := by
  -- Phase 1a: k rounds of R4/R3
  rw [show 2 * k + 1 = 1 + 2 * k from by ring,
      show 2 * k + 3 = (k + 3) + k from by ring]
  apply stepStar_stepPlus_stepPlus (r4r3_chain k 0 1 (k + 3))
  -- At (0, 0, k, 1, k+3): R4 step (for ⊢⁺)
  rw [show k + 3 = (k + 2) + 1 from by ring]
  step fm
  -- At (0, 1, k+1, 1, k+2): R4 step
  rw [show k + 2 = (k + 1) + 1 from by ring]
  step fm
  -- Now at (0, 2, 0+k+1+1, 1, k+1) which is (0, 2, k+2, 1, k+1)
  rw [show 0 + k + 1 + 1 = k + 2 from by ring]
  apply stepStar_trans (r1r2r2_chain (k + 2) 1 (k + 1))
  rw [show 1 + 3 * (k + 2) = (3 * k + 3) + 4 from by ring,
      show k + 1 + 2 * (k + 2) = 3 * k + 5 from by ring]
  step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d, q = ⟨0, 0, 0, d, d + 2⟩)
  · intro c ⟨d, hq⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      exact ⟨⟨0, 0, 0, 3*K + 2, 3*K + 4⟩,
             ⟨3*K + 2, by ring_nf⟩, even_trans⟩
    · subst hK
      exact ⟨⟨0, 0, 0, 3*K + 3, 3*K + 5⟩,
             ⟨3*K + 3, by ring_nf⟩, odd_trans⟩
  · exact ⟨0, rfl⟩
