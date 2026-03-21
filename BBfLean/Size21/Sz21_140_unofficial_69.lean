import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #69: [4/15, 33/14, 5/2, 7/11, 28/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_69

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R2R1 chain: k rounds of (R2, R1)
-- Each round: R2 on (A+1, 0, C, D+1, E) → (A, 1, C, D, E+1)
--             R1 on (A, 1, C+1, D, E+1) → (A+2, 0, C, D, E+1)
-- Net: a+1, c-1, d-1, e+1
theorem r2r1_chain : ∀ k, ∀ a c d e, ⟨a+2, 0, c+k, d+1+k, e⟩ [fm]⊢* ⟨a+2+k, 0, c, d+1, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + 1 + (k + 1) = (d + 1 + k) + 1 from by ring]
  step fm
  step fm
  rw [show a + 2 + (k + 1) = (a + 1) + 2 + k from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  exact ih (a + 1) c d (e + 1)

-- a → c transfer (R3 repeated): when b=0, d=0
theorem a_to_c : ∀ k, ∀ a c, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- e → d transfer (R4 repeated): when a=0, b=0
theorem e_to_d : ∀ k, ∀ d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Main transition: (2, 0, n, n+1, 0) ⊢⁺ (2, 0, n+1, n+2, 0)
theorem main_trans (n : ℕ) : ⟨2, 0, n, n+1, 0⟩ [fm]⊢⁺ ⟨2, 0, n+1, n+2, 0⟩ := by
  -- Phase 1: n R2R1 pairs: (2, 0, n, n+1, 0) →* (n+2, 0, 0, 1, n)
  -- r2r1_chain n 0 0 0 0 gives: (0+2, 0, 0+n, 0+1+n, 0) →* (0+2+n, 0, 0, 0+1, 0+n)
  -- = (2, 0, n, 1+n, 0) →* (2+n, 0, 0, 1, n)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2+n, 0, 0, 1, n⟩)
  · rw [show n + 1 = 1 + n from by ring]
    have h := @r2r1_chain n 0 0 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R2: (2+n, 0, 0, 1, n) → (1+n, 1, 0, 0, n+1)
  -- Rewrite to match R2 pattern: ((1+n)+1, 0, 0, 0+1, n) → (1+n, 0+1, 0, 0, n+1)
  apply step_stepStar_stepPlus (c₂ := ⟨n+1, 1, 0, 0, n+1⟩)
  · rw [show (2 + n) = (n + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    show fm ⟨(n+1)+1, 0, 0, 0+1, n⟩ = some ⟨n+1, 0+1, 0, 0, n+1⟩
    simp [fm]
  -- Phase 3: R3, R1: (n+1, 1, 0, 0, n+1) → (n, 1, 1, 0, n+1) → (n+2, 0, 0, 0, n+1)
  apply stepStar_trans (c₂ := ⟨n+2, 0, 0, 0, n+1⟩)
  · -- R3: (n+1, 1, 0, 0, n+1) matches (a+1, b, c, d, e) → (a, b, c+1, d, e)
    -- but R1 fires first if b>=1 and c>=1. b=1, c=0, so R1 doesn't fire.
    -- R2: a+1 and d+1? a=n+1>=1, d=0, so no.
    -- R3: a+1? a=n+1>=1, so yes. → (n, 1, 1, 0, n+1)
    -- R1: b=1>=1, c=1>=1, so yes. → (n+2, 0, 0, 0, n+1)
    have step1 : ⟨n+1, 1, 0, 0, n+1⟩ [fm]⊢ ⟨n, 1, 1, 0, n+1⟩ := by
      show fm ⟨n + 1, 1, 0, 0, n + 1⟩ = some ⟨n, 1, 1, 0, n + 1⟩
      simp [fm]
    have step2 : ⟨n, 1, 1, 0, n+1⟩ [fm]⊢ ⟨n+2, 0, 0, 0, n+1⟩ := by
      show fm ⟨n, 0 + 1, 0 + 1, 0, n + 1⟩ = some ⟨n + 2, 0, 0, 0, n + 1⟩
      simp [fm]
    exact stepStar_trans (step_stepStar step1) (step_stepStar step2)
  -- Phase 4: R3 × (n+2): (n+2, 0, 0, 0, n+1) →* (0, 0, n+2, 0, n+1)
  apply stepStar_trans (c₂ := ⟨0, 0, n+2, 0, n+1⟩)
  · have h := @a_to_c (n + 1) (n + 2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 5: R4 × (n+1): (0, 0, n+2, 0, n+1) →* (0, 0, n+2, n+1, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, n+2, n+1, 0⟩)
  · have h := @e_to_d (n + 2) (n + 1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 6: R5: (0, 0, n+2, n+1, 0) → (2, 0, n+1, n+2, 0)
  -- (0, 0, (n+1)+1, n+1, 0) matches R5: (a, b, c+1, d, e) → (a+2, b, c, d+1, e)
  have step6 : ⟨0, 0, n+2, n+1, 0⟩ [fm]⊢ ⟨2, 0, n+1, n+2, 0⟩ := by
    show fm ⟨0, 0, (n+1)+1, n+1, 0⟩ = some ⟨0+2, 0, n+1, (n+1)+1, 0⟩
    simp [fm]
  exact step_stepStar step6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 2, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨2, 0, n+1, n+2, 0⟩) 0
  intro n; exact ⟨n+1, main_trans (n+1)⟩
