import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #59: [4/15, 1/14, 33/2, 7/3, 50/77]

Vector representation:
```
 2 -1 -1  0  0
-1  0  0 -1  0
-1  1  0  0  1
 0 -1  0  1  0
 1  0  2 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_59

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- Phase 1: R3 repeated: (a+k, b, 0, 0, e) →* (a, b+k, 0, 0, e+k)
theorem a_to_be : ⟨a+k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b+k, 0, 0, e+k⟩ := by
  have many_step : ∀ k a b e, ⟨a+k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b+k, 0, 0, e+k⟩ := by
    intro k; induction' k with k h <;> intro a b e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a b e

-- Phase 2: R4 repeated: (0, b+k, 0, d, e) →* (0, b, 0, d+k, e)
theorem b_to_d : ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d+k, e⟩ := by
  have many_step : ∀ k b d, ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- Phase 3a: R5+R2 pairs: (0, 0, c, d+2*k, e+k) →* (0, 0, c+2*k, d, e)
theorem r5r2_pairs : ⟨0, 0, c, d+2*k, e+k⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e⟩ := by
  have many_step : ∀ k c d e, ⟨0, 0, c, d+2*k, e+k⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- Phase 3c: R3+R1 chain: (a+1, 0, c+k, 0, e) →* (a+1+k, 0, c, 0, e+k)
theorem r3r1_chain : ⟨a+1, 0, c+k, 0, e⟩ [fm]⊢* ⟨a+1+k, 0, c, 0, e+k⟩ := by
  have many_step : ∀ k a c e, ⟨a+1, 0, c+k, 0, e⟩ [fm]⊢* ⟨a+1+k, 0, c, 0, e+k⟩ := by
    intro k; induction' k with k h <;> intro a c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    -- R3: (a+1, 0, (c+k)+1, 0, e) → (a, 1, (c+k)+1, 0, e+1)
    -- But wait, R1 has priority: needs b≥1 AND c≥1. b=0 here, so R1 doesn't match.
    -- R2: needs a≥1 AND d≥1. d=0 here, so R2 doesn't match.
    -- R3: needs a≥1. a+1≥1. Fires: (a, 1, (c+k)+1, 0, e+1)
    step fm
    -- Now: (a, 1, (c+k)+1, 0, e+1)
    -- R1: b=1≥1, c=(c+k)+1≥1. Fires: (a+2, 0, c+k, 0, e+1)
    step fm
    -- Now: (a+2, 0, c+k, 0, e+1) = ((a+1)+1, 0, c+k, 0, e+1)
    -- Apply IH: ((a+1)+1, 0, c+k, 0, e+1) →* ((a+1)+1+k, 0, c, 0, (e+1)+k)
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a c e

-- Main transition: (2*n+3, 0, 0, 0, e) ⊢⁺ (2*n+5, 0, 0, 0, e+3*n+5)
-- Phases:
-- P1: R3 x (2n+3): (2n+3, 0, 0, 0, e) →* (0, 2n+3, 0, 0, e+2n+3)
-- P2: R4 x (2n+3): (0, 2n+3, 0, 0, e+2n+3) →* (0, 0, 0, 2n+3, e+2n+3)
-- P3a: (R5+R2) x (n+1): (0, 0, 0, 2n+3, e+2n+3) →* (0, 0, 2n+2, 1, e+n+2)
-- P3b: R5: (0, 0, 2n+2, 1, e+n+2) → (1, 0, 2n+4, 0, e+n+1)
-- P3c: (R3+R1) x (2n+4): (1, 0, 2n+4, 0, e+n+1) →* (2n+5, 0, 0, 0, e+3n+5)
theorem main_trans (n : ℕ) (e : ℕ) : ⟨2*n+3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2*n+5, 0, 0, 0, e+3*n+5⟩ := by
  -- Phase 1: (2n+3, 0, 0, 0, e) →* (0, 2n+3, 0, 0, e+2n+3)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*n+3, 0, 0, e+2*n+3⟩)
  · have h := @a_to_be 0 (2*n+3) 0 e
    rw [show 0 + (2 * n + 3) = 2 * n + 3 from by ring] at h; exact h
  -- Phase 2: (0, 2n+3, 0, 0, e+2n+3) →* (0, 0, 0, 2n+3, e+2n+3)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 2*n+3, e+2*n+3⟩)
  · have h := @b_to_d 0 (2*n+3) 0 (e+2*n+3)
    rw [show 0 + (2 * n + 3) = 2 * n + 3 from by ring] at h; exact h
  -- Phase 3a: (R5+R2) x (n+1): (0, 0, 0, 2n+3, e+2n+3) →* (0, 0, 2n+2, 1, e+n+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*n+2, 1, e+n+2⟩)
  · have h := @r5r2_pairs 0 1 (n+1) (e+n+2)
    rw [show 1 + 2 * (n + 1) = 2 * n + 3 from by ring,
        show e + n + 2 + (n + 1) = e + 2 * n + 3 from by ring,
        show 0 + 2 * (n + 1) = 2 * n + 2 from by ring] at h; exact h
  -- Phase 3b+3c: R5 step then R3+R1 chain
  -- (0, 0, 2n+2, 1, e+n+2) → (1, 0, 2n+4, 0, e+n+1) →* (2n+5, 0, 0, 0, e+3n+5)
  rw [show e + n + 2 = (e + n + 1) + 1 from by ring]
  step fm
  have h := @r3r1_chain 0 0 (2*n+4) (e+n+1)
  rw [show 0 + 1 = 1 from by ring,
      show 0 + (2 * n + 4) = 2 * n + 4 from by ring,
      show 0 + 1 + (2 * n + 4) = 2 * n + 5 from by ring,
      show e + n + 1 + (2 * n + 4) = e + 3 * n + 5 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1, 0, 0, 0, 0) →* (3, 0, 0, 0, 2) in 7 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 2⟩) (by execute fm 7)
  -- Canonical form: (2n+3, 0, 0, 0, e) with transition (n, e) → (n+1, e+3n+5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨2*n+3, 0, 0, 0, e⟩) ⟨0, 2⟩
  intro ⟨n, e⟩; exact ⟨⟨n+1, e+3*n+5⟩, main_trans n e⟩

end Sz21_140_unofficial_59
