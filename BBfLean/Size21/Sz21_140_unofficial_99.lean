import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #99: [7/15, 2/3, 99/14, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  0
-1  2  0 -1  1
 0  0  1  0 -1
-1  1  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_99

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

-- R4 repeated: e → c (when b=0, d=0)
theorem e_to_c : ∀ k c e, ⟨a, 0, c, 0, e+k⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3/R1/R1 chain
theorem r3r1r1_chain : ∀ k, ∀ a c d e, ⟨a+k, 0, c+2*k, d+1, e⟩ [fm]⊢* ⟨a, 0, c, d+1+k, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
  step fm
  step fm
  step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (h a c (d + 1) (e + 1))
  ring_nf; finish

-- R3/R1/R2: (1, 0, 1, d+1, e) →* (1, 0, 0, d+1, e+1)
theorem r3r1r2_step : ∀ d e, ⟨1, 0, 1, d+1, e⟩ [fm]⊢* ⟨1, 0, 0, d+1, e+1⟩ := by
  intro d e
  step fm
  step fm
  step fm
  finish

-- R3/R2/R2 chain
theorem r3r2r2_chain : ∀ k, ∀ a d e, ⟨a+1, 0, 0, d+k, e⟩ [fm]⊢* ⟨a+1+k, 0, 0, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  step fm
  step fm
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans (h (a + 1) d (e + 1))
  ring_nf; finish

-- Whole transition as stepPlus using explicit intermediate states
theorem main_trans (n : ℕ) : ⟨n+2, 0, 2*n+2, 0, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 2*n+4, 0, 0⟩ := by
  -- Step 1: R5 step gives us stepPlus start
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(n + 1) + 1, 0, 2 * n + 2, 0, 0⟩ = some ⟨n + 1, 1, 2 * n + 2, 1, 1⟩
    simp [fm]
  -- Now need: (n+1, 1, 2n+2, 1, 1) ⊢* (n+3, 0, 2n+4, 0, 0)
  -- Step 2: R1 step
  apply stepStar_trans
  · show ⟨n+1, 1, 2*n+2, 1, 1⟩ [fm]⊢* ⟨n+1, 0, 2*n+1, 2, 1⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
    step fm; finish
  -- Step 3: n rounds of R3/R1/R1
  -- (n+1, 0, 2n+1, 2, 1) →* (1, 0, 1, n+2, n+1)
  apply stepStar_trans
  · show ⟨n+1, 0, 2*n+1, 2, 1⟩ [fm]⊢* ⟨1, 0, 1, n+2, n+1⟩
    have h := r3r1r1_chain n 1 1 1 1
    rw [show 1 + 2 * n = 2 * n + 1 from by ring,
        show 1 + 1 + n = n + 2 from by ring,
        show 1 + n = n + 1 from by ring] at h
    convert h using 2
  -- Step 4: R3/R1/R2
  -- (1, 0, 1, n+2, n+1) →* (1, 0, 0, n+2, n+2)
  apply stepStar_trans
  · show ⟨1, 0, 1, n+2, n+1⟩ [fm]⊢* ⟨1, 0, 0, n+2, n+2⟩
    have h := r3r1r2_step (n + 1) (n + 1)
    rw [show n + 1 + 1 = n + 2 from by ring] at h
    exact h
  -- Step 5: R3/R2/R2 chain (n+2 rounds)
  -- (1, 0, 0, n+2, n+2) →* (n+3, 0, 0, 0, 2n+4)
  apply stepStar_trans
  · show ⟨1, 0, 0, n+2, n+2⟩ [fm]⊢* ⟨n+3, 0, 0, 0, 2*n+4⟩
    have h := r3r2r2_chain (n + 2) 0 0 (n + 2)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Step 6: R4 repeated
  -- (n+3, 0, 0, 0, 2n+4) →* (n+3, 0, 2n+4, 0, 0)
  have h := @e_to_c (n + 3) (2 * n + 4) 0 0
  simp only [Nat.zero_add] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+2, 0, 2*n+2, 0, 0⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
