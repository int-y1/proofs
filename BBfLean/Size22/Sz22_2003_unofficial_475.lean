import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #475: [28/15, 3/154, 35/2, 11/5, 6/7]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0 -1 -1
-1  0  1  1  0
 0  0 -1  0  1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_475

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R3 chain: a steps of R3 with arbitrary c
theorem r3_chain : ∀ k, ∀ a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1) (d + 1))
  ring_nf; finish

-- R4 chain: c steps of R4
theorem r4_chain : ∀ k, ∀ d e, ⟨0, 0, k, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (ih d (e + 1))
  ring_nf; finish

-- R5/R2 chain: k rounds of (R5, R2)
theorem r5r2_chain : ∀ k, ∀ b d, ⟨0, b, 0, d + 2 * k, k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring]
  step fm
  step fm
  rw [show b + 1 + 1 = b + 2 from by ring]
  apply stepStar_trans (ih (b + 2) d)
  ring_nf; finish

-- R3/R1 chain: k+1 rounds of (R3, R1)
theorem r3r1_chain : ∀ k, ∀ a d, ⟨a + 1, k + 1, 0, d, 0⟩ [fm]⊢* ⟨a + k + 2, 0, 0, d + 2 * k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; step fm; ring_nf; finish
  rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
  step fm
  step fm
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans (ih (a + 1) (d + 2))
  ring_nf; finish

-- Main transition
theorem main_trans (a d : ℕ) : ⟨a + 2, 0, 0, d + a + 3, 0⟩ [fm]⊢⁺ ⟨2 * a + 6, 0, 0, d + 4 * a + 10, 0⟩ := by
  -- Phase 1: R3 chain (a+2 steps)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, a + 2, d + 2 * a + 5, 0⟩)
  · have h := r3_chain (a + 2) 0 0 (d + a + 3)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 2: R4 chain (a+2 steps)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, d + 2 * a + 5, a + 2⟩)
  · have h := r4_chain (a + 2) (d + 2 * a + 5) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5/R2 chain (a+2 rounds)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2 * a + 4, 0, d + 1, 0⟩)
  · rw [show d + 2 * a + 5 = (d + 1) + 2 * (a + 2) from by ring]
    have h := r5r2_chain (a + 2) 0 (d + 1)
    simp only [Nat.zero_add] at h
    convert h using 2
  -- Phase 4: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨1, 2 * a + 5, 0, d, 0⟩)
  · simp [fm]
  -- Phase 5: R3/R1 chain (2a+5 rounds)
  rw [show 2 * a + 5 = (2 * a + 4) + 1 from by ring]
  have h := r3r1_chain (2 * a + 4) 0 d
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 2, 0, 0, d + a + 3, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩
  exact ⟨⟨2 * a + 4, d + 2 * a + 3⟩, by convert main_trans a d using 2; ring_nf⟩

end Sz22_2003_unofficial_475
