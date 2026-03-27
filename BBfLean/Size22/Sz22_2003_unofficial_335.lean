import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #335: [189/10, 121/2, 2/33, 5/7, 10/11]

Vector representation:
```
-1  3 -1  1  0
-1  0  0  0  2
 1 -1  0  0 -1
 0  0  1 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_335

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- Phase 1: transfer d to c (rule 4)
theorem d_to_c : ∀ k c e,
    ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- Phase 2: climb loop (rule 3 + rule 1), k iterations
-- Parametrized with all free vars to allow clean induction.
-- (0, b+1, c+k, d, e+k) ⊢* (0, b+2k+1, c, d+k, e)
theorem climb_loop : ∀ k b c d e,
    ⟨0, b + 1, c + k, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k + 1, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 3 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    ring_nf; finish

-- Full climb: rule 5, rule 1, then climb_loop
-- (0, 0, c, 0, e+c+1) ⊢* (0, 2c+3, 0, c+1, e)
theorem climb (c e : ℕ) :
    ⟨0, 0, c, 0, e + c + 1⟩ [fm]⊢* ⟨0, 2 * c + 3, 0, c + 1, e⟩ := by
  rw [show e + c + 1 = (e + c) + 1 from by ring]
  step fm; step fm
  have h := climb_loop c 2 0 1 e
  simp only [Nat.zero_add] at h
  rw [show c + 1 = 1 + c from by ring,
      show 2 * c + 3 = 2 + 2 * c + 1 from by ring]
  exact h

-- Phase 3: drain b (rule 3 + rule 2)
-- (0, k, 0, d+1, e+1) ⊢* (0, 0, 0, d+1, e+k+1)
theorem drain_b : ∀ k d e,
    ⟨0, k, 0, d + 1, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 1, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; step fm
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, d, e+d+2) ⊢⁺ (0, 0, 0, d+1, e+2*d+4)
theorem main_trans (d e : ℕ) :
    ⟨0, 0, 0, d, e + d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 1, e + 2 * d + 4⟩ := by
  -- Phase 1: d_to_c
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_c d 0 (e + d + 2)
    simp only [Nat.zero_add] at h; exact h
  -- After d_to_c: (0, 0, d, 0, e+d+2)
  -- Phase 2: climb
  apply stepStar_stepPlus_stepPlus
  · have h := climb d (e + 1)
    rw [show e + 1 + d + 1 = e + d + 2 from by ring] at h; exact h
  -- After climb: (0, 2d+3, 0, d+1, e+1)
  -- Phase 3: drain_b; first step manually to get stepPlus
  -- (0, 2d+3, 0, d+1, e+1): rule 3 fires (b≥1, e≥1)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * d + 3, 0, d + 1, e + 1⟩ = _; rfl
  -- After rule 3: (1, 2d+2, 0, d+1, e)
  -- rule 2: (0, 2d+2, 0, d+1, e+2)
  step fm
  -- Now drain remaining (2d+2)
  rw [show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (drain_b (2 * d + 2) d (e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩)
  · execute fm 1
  exact progress_nonhalt (fm := fm)
    (fun c ↦ ∃ d e, c = (⟨0, 0, 0, d, e + d + 2⟩ : Q))
    (fun c ⟨d, e, hc⟩ ↦ ⟨⟨0, 0, 0, d + 1, e + 2 * d + 4⟩,
      ⟨d + 1, e + d + 1, by ring_nf⟩, hc ▸ main_trans d e⟩)
    ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_335
