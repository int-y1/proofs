import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #11: [1/105, 45/22, 2/3, 49/2, 363/7]

Vector representation:
```
 0 -1 -1 -1  0
-1  2  1  0 -1
 1 -1  0  0  0
-1  0  0  2  0
 0  1  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_11

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R1,R2 chain: k rounds of (R1 then R2) consuming e register
theorem r1r2_chain : ∀ k, ∀ b c e, ⟨1, b, c, 0, e+k⟩ [fm]⊢* ⟨1, b+k, c+k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro b c e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  rw [show b + 2 = (b + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 chain: b → a transfer
theorem b_to_a : ∀ k, ∀ a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a+k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 chain: a → d transfer (each a gives 2 d)
theorem a_to_d : ∀ k, ∀ c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4,R0 chain: paired steps consuming c and d, producing e
theorem r4r0_chain : ∀ k, ∀ c d e, ⟨0, 0, c+k, d+2*k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  rw [show (d + 2 * k) + 2 = ((d + 2 * k) + 1) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Cleanup: (0, 0, 0, 2, 2*e) → (1, 0, 0, 0, 2*e+1) in 5 steps
theorem cleanup : ⟨0, 0, 0, 2, 2*e⟩ [fm]⊢* ⟨1, 0, 0, 0, 2*e+1⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  step fm
  rw [show 2 * e + 2 = (2 * e + 1) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  step fm
  finish

-- Main transition: (1, 0, 0, 0, e+1) ⊢⁺ (1, 0, 0, 0, 2*e+3)
theorem main_trans (e : ℕ) : ⟨1, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2*e+3⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, e, e, 0, 1⟩)
  · have h := r1r2_chain e 0 0 1
    simp only [Nat.zero_add] at h
    rw [show 1 + e = e + 1 from by ring] at h
    exact h
  apply step_stepStar_stepPlus (c₂ := ⟨0, e+2, e+1, 0, 0⟩)
  · show fm ⟨0 + 1, e, e, 0, 0 + 1⟩ = some ⟨0, e + 2, e + 1, 0, 0⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨e+2, 0, e+1, 0, 0⟩)
  · have h := b_to_a (e+2) 0 (e+1)
    simp only [Nat.zero_add] at h
    exact h
  apply stepStar_trans (c₂ := ⟨0, 0, e+1, 2*(e+2), 0⟩)
  · have h := a_to_d (e+2) (e+1) 0
    simp only [Nat.zero_add] at h
    exact h
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2, 2*(e+1)⟩)
  · have h := r4r0_chain (e+1) 0 2 0
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * (e + 1) = 2 * (e + 2) from by ring] at h
    exact h
  exact @cleanup (e+1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨1, 0, 0, 0, e+1⟩) 0
  intro e; refine ⟨2*e+2, ?_⟩
  exact main_trans e

end Sz22_2003_unofficial_11
