import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #476: [28/15, 3/154, 5/2, 121/5, 6/11]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0 -1 -1
-1  0  1  0  0
 0  0 -1  0  2
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_476

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R3 chain
theorem a_to_c : ∀ k, ∀ a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2: R4 chain
theorem c_to_e : ∀ k, ∀ c d e, ⟨0, 0, c+k, d, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 3: R5/R2 pairs
theorem r5r2_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d+k, e+2*k⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 5: R3,R1 chain
theorem r3r1_chain : ∀ k, ∀ a b d, ⟨a+2, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+2+k, b, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h (a+1) _ _)
  ring_nf; finish

-- Main transition: (a+2, 0, 0, a+1, 0) ⊢⁺ (2*a+4, 0, 0, 2*a+3, 0)
theorem main_trans (a : ℕ) : ⟨a+2, 0, 0, a+1, 0⟩ [fm]⊢⁺ ⟨2*a+4, 0, 0, 2*a+3, 0⟩ := by
  -- Phase 1: (a+2, 0, 0, a+1, 0) →* (0, 0, a+2, a+1, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := a_to_c (a+2) 0 0 (a+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: first R4 step for ⊢⁺, then remaining R4 steps
  -- (0, 0, a+2, a+1, 0) → (0, 0, a+1, a+1, 2) →* (0, 0, 0, a+1, 2*a+4)
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus
  · step fm; finish
  apply stepStar_trans
  · have h := c_to_e (a+1) 0 (a+1) 2
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * (a + 1) = 2 * a + 4 from by ring] at h
    exact h
  -- Phase 3: R5/R2 pairs: (0, 0, 0, a+1, 2*a+4) →* (0, 2*a+2, 0, 0, 2)
  apply stepStar_trans
  · have h := r5r2_chain (a+1) 0 0 2
    simp only [Nat.zero_add] at h
    rw [show 2 * (a + 1) = 2 * a + 2 from by ring,
        show 2 + (2 * a + 2) = 2 * a + 4 from by ring] at h
    exact h
  -- Phase 4: 6-step sequence: (0, 2*a+2, 0, 0, 2) → ... → (2, 2*a+2, 0, 1, 0)
  step fm; step fm; step fm; step fm; step fm; step fm
  -- Phase 5: R3/R1 chain: (2, 2*a+2, 0, 1, 0) →* (2*a+4, 0, 0, 2*a+3, 0)
  have h := r3r1_chain (2*a+2) 0 0 1
  simp only [Nat.zero_add] at h
  rw [show 0 + 2 + (2 * a + 2) = 2 * a + 4 from by ring,
      show 1 + (2 * a + 2) = 2 * a + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun a ↦ ⟨a+2, 0, 0, a+1, 0⟩) 0
  intro a; exists 2*a+2; exact main_trans a

end Sz22_2003_unofficial_476
