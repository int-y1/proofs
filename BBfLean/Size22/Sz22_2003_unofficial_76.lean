import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #76: [1/18, 35/2, 26/55, 363/7, 2/39]

Vector representation:
```
-1 -2  0  0  0  0
-1  0  1  1  0  0
 1  0 -1  0 -1  1
 0  1  0 -1  2  0
 1 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_76

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+2, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- Canonical form: (1, 0, 0, 0, 3*n, 2*n), transition n → 2*n+1

-- Phase 1: R2-R3 interleaved chain (induction on e)
theorem r2r3_chain : ∀ e, ∀ d f,
    ⟨1, 0, 0, d, e, f⟩ [fm]⊢* ⟨1, 0, 0, d+e, 0, f+e⟩ := by
  intro e; induction' e with e ih <;> intro d f
  · exists 0
  rw [show d + (e + 1) = (d + 1) + e from by ring,
      show f + (e + 1) = (f + 1) + e from by ring]
  step fm; step fm
  exact ih (d+1) (f+1)

-- Phase 2: R4 drain
theorem r4_drain : ∀ d, ∀ b e f,
    ⟨0, b, 0, d, e, f⟩ [fm]⊢* ⟨0, b+d, 0, 0, e+2*d, f⟩ := by
  intro d; induction' d with d ih <;> intro b e f
  · exists 0
  rw [show b + (d + 1) = (b + 1) + d from by ring,
      show e + 2 * (d + 1) = (e + 2) + 2 * d from by ring]
  step fm
  exact ih (b+1) (e+2) f

-- Phase 3: R5-R1 drain pairs
theorem r5r1_pairs : ∀ k, ∀ e f,
    ⟨0, 3*k+1, 0, 0, e, f+k+1⟩ [fm]⊢* ⟨1, 0, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro e f
  · step fm; finish
  rw [show 3 * (k + 1) + 1 = (3 * k + 1 + 2) + 1 from by ring,
      show f + (k + 1) + 1 = (f + k + 1) + 1 from by ring]
  step fm
  rw [show 3 * k + 1 + 2 = (3 * k + 1) + 2 from by ring]
  step fm
  exact ih e f

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, 0, 3*n, 2*n⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 3*(2*n+1), 2*(2*n+1)⟩ := by
  -- Phase 1: R2-R3 chain
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 0, 0, 3*n, 0, 5*n⟩)
  · have h := r2r3_chain (3*n) 0 (2*n)
    simp only [Nat.zero_add] at h
    rw [show (5 : ℕ)*n = 2*n + 3*n from by omega]; exact h
  -- Phase 2a: R2
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, 1, 3*n+1, 0, 5*n⟩)
  · unfold fm; simp
  -- Phase 2b: R4
  apply stepStar_trans (c₂ := ⟨0, 1, 1, 3*n, 2, 5*n⟩)
  · apply step_stepStar; rfl
  -- Phase 2c: R3 R2 R3 R2
  apply stepStar_trans (c₂ := ⟨0, 1, 1, 3*n+2, 0, 5*n+2⟩)
  · step fm; step fm; step fm; step fm; finish
  -- Phase 2d: R4 R3 R1
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 3*n+1, 1, 5*n+3⟩)
  · step fm; step fm; step fm; finish
  -- Phase 3: R4 drain
  apply stepStar_trans (c₂ := ⟨0, 3*n+1, 0, 0, 6*n+3, 5*n+3⟩)
  · have h := r4_drain (3*n+1) 0 1 (5*n+3)
    simp only [Nat.zero_add] at h
    rw [show (6 : ℕ)*n+3 = 1+2*(3*n+1) from by omega]; exact h
  -- Phase 4: R5-R1 pairs
  -- Need: (0, 3n+1, 0, 0, 6n+3, 5n+3) →* (1, 0, 0, 0, 6n+3, 4n+2)
  -- r5r1_pairs n (6n+3) (4n+1): (0, 3n+1, 0, 0, 6n+3, 4n+1+n+1) →* (1, 0, 0, 0, 6n+3, 4n+1)
  -- 4n+1+n+1 = 5n+2, but we need 5n+3. So let me use f = 4n+2.
  -- r5r1_pairs n (6n+3) (4n+2): (0, 3n+1, 0, 0, 6n+3, 4n+2+n+1) →* (1, 0, 0, 0, 6n+3, 4n+2)
  -- 4n+2+n+1 = 5n+3 ✓
  rw [show (5 : ℕ)*n+3 = 4*n+2+n+1 from by ring,
      show (6 : ℕ)*n+3 = 3*(2*n+1) from by ring,
      show (4 : ℕ)*n+2 = 2*(2*n+1) from by ring]
  exact r5r1_pairs n (3*(2*n+1)) (2*(2*n+1))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, 0, 3*n, 2*n⟩) 0
  intro n; exact ⟨2*n+1, main_trans n⟩
