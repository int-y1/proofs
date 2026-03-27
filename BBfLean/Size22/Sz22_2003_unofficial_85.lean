import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #85: [1/30, 1323/2, 2/77, 5/7, 22/3]

Vector representation:
```
-1 -1 -1  0  0
-1  3  0  2  0
 1  0  0 -1 -1
 0  0  1 -1  0
 1 -1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude (claude-opus-4-6)
-/

namespace Sz22_2003_unofficial_85

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- Helper: fm applied to (a+1, b, 0, d, e) = R2
theorem fm_r2 (a b d e : ℕ) : fm ⟨a+1, b, 0, d, e⟩ = some ⟨a, b+3, 0, d+2, e⟩ := by
  simp [fm]

-- R3/R2 chain: each round R3 then R2. Net: b += 3, d += 1, e -= 1.
theorem r3r2_chain : ∀ k, ∀ b d,
    ⟨0, b, 0, d+1, k+1⟩ [fm]⊢* ⟨0, b+3*(k+1), 0, d+k+2, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · step fm
    -- State: (1, b, 0, d, 0). R2 fires.
    apply stepStar_trans (step_stepStar (fm_r2 0 b d 0))
    ring_nf; finish
  rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
  step fm
  -- State: (1, b, 0, d, k+1). R2 fires since c=0.
  apply stepStar_trans (step_stepStar (fm_r2 0 b d (k+1)))
  apply stepStar_trans (ih (b + 3) (d + 1))
  ring_nf; finish

-- R4 chain: d transfers to c.
theorem r4_chain : ∀ k, ∀ b c,
    ⟨0, b, c, k, 0⟩ [fm]⊢* ⟨0, b, c+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih b (c + 1))
  ring_nf; finish

-- R5/R1 chain: each round R5 then R1. Net: b -= 2, c -= 1, e += 1.
-- State: (0, b+2*k, k, 0, e) with b+2*k >= 2 and k >= 1 for R5/R1.
theorem r5r1_chain : ∀ k, ∀ b e,
    ⟨0, b+2*k, k, 0, e⟩ [fm]⊢* ⟨0, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring]
  step fm
  -- State: (1, b+2*k+1, k+1, 0, e+1). R1 matches: a+1=1, b+1=b+2*k+1, c+1=k+1.
  rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
  step fm
  -- State: (0, b+2*k, k, 0, e+1).
  apply stepStar_trans (ih b (e + 1))
  ring_nf; finish

-- Main transition: (0, b+1, 0, 0, e+2) ⊢⁺ (0, b+e+2, 0, 0, e+5)
theorem main_trans (b e : ℕ) :
    ⟨0, b+1, 0, 0, e+2⟩ [fm]⊢⁺ ⟨0, b+e+2, 0, 0, e+5⟩ := by
  -- Phase 1: R5 -> (1, b, 0, 0, e+3)
  apply step_stepStar_stepPlus (c₂ := ⟨1, b, 0, 0, e+3⟩)
  · show fm ⟨0, b+1, 0, 0, e+2⟩ = some ⟨1, b, 0, 0, e+3⟩; simp [fm]
  -- Phase 2: R2 -> (0, b+3, 0, 2, e+3)
  apply stepStar_trans (step_stepStar (fm_r2 0 b 0 (e+3)))
  -- Phase 3: R3/R2 chain with e+3 rounds: -> (0, b+3+3*(e+3), 0, 1+(e+2)+2, 0) = (0, b+3e+12, 0, e+5, 0)
  apply stepStar_trans (c₂ := ⟨0, b+3*e+12, 0, e+5, 0⟩)
  · have h := r3r2_chain (e+2) (b+3) 1
    rw [show e + 2 + 1 = e + 3 from by ring,
        show b + 3 + 3 * (e + 3) = b + 3 * e + 12 from by ring,
        show 1 + (e + 2) + 2 = e + 5 from by ring] at h; exact h
  -- Phase 4: R4 chain with e+5 steps: -> (0, b+3e+12, e+5, 0, 0)
  apply stepStar_trans (c₂ := ⟨0, b+3*e+12, e+5, 0, 0⟩)
  · have h := r4_chain (e+5) (b+3*e+12) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 5: R5/R1 chain with e+5 rounds: -> (0, b+e+2, 0, 0, e+5)
  have h := r5r1_chain (e+5) (b+e+2) 0
  rw [show b + e + 2 + 2 * (e + 5) = b + 3 * e + 12 from by ring,
      show 0 + (e + 5) = e + 5 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 2⟩) (by execute fm 17)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨b, e⟩ ↦ ⟨0, b+1, 0, 0, e+2⟩) ⟨0, 0⟩
  intro ⟨b, e⟩
  exact ⟨⟨b+e+1, e+3⟩, main_trans b e⟩
