import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #206: [1/6, 385/2, 14/65, 39/7, 4/33]

Vector representation:
```
-1 -1  0  0  0  0
-1  0  1  1  1  0
 1  0 -1  1  0 -1
 0  1  0 -1  0  1
 2 -1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_206

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- R4 loop with c=0: (0, b, 0, d+k, e, f) →* (0, b+k, 0, d, e, f+k)
theorem r4_loop : ∀ k, ∀ b d e f, ⟨(0 : ℕ), b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · simp; exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R5-R1-R1 loop: (0, 3*k+1, 0, 0, k+1+j, f) →* (2, 0, 0, 0, j, f)
theorem r5r1r1_loop : ∀ k, ∀ j f, ⟨(0 : ℕ), 3 * k + 1, 0, 0, k + 1 + j, f⟩ [fm]⊢* ⟨2, 0, 0, 0, j, f⟩ := by
  intro k; induction' k with k ih <;> intro j f
  · -- (0, 1, 0, 0, 1+j, f) → R5 → (2, 0, 0, 0, j, f)
    simp
    rw [show 1 + j = j + 1 from by ring]
    step fm; finish
  · -- (0, 3*(k+1)+1, 0, 0, (k+1)+1+j, f)
    rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 1 + 1 + 1 from by ring,
        show (k + 1) + 1 + j = (k + 1 + j) + 1 from by ring]
    step fm  -- R5
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih j f)
    finish

-- R3-R2 loop: (0, 0, 2, d, e, f+k) →* (0, 0, 2, d+2*k, e+k, f)
theorem r3r2_loop : ∀ k, ∀ d e f, ⟨(0 : ℕ), 0, 2, d, e, f + k⟩ [fm]⊢* ⟨0, 0, 2, d + 2 * k, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · simp; exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 1: consume c=2 via R4-R3-R1 twice
-- (0, 0, 2, d+1, e, 0) →* (0, 0, 0, d+1, e, 0) in 6 steps
theorem phase1 (d e : ℕ) :
    ⟨(0 : ℕ), 0, 2, d + 1, e, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 1, e, 0⟩ := by
  -- R4: (0, 1, 2, d, e, 1)
  step fm
  -- R3: (1, 1, 1, d+1, e, 0)
  step fm
  -- R1: (0, 0, 1, d+1, e, 0)
  step fm
  -- R4: (0, 1, 1, d, e, 1)
  step fm
  -- R3: (1, 1, 0, d+1, e, 0)
  step fm
  -- R1: (0, 0, 0, d+1, e, 0)
  step fm
  finish

-- Main transition: (0, 0, 2, 3*k+1, 2*k+1, 0) ⊢⁺ (0, 0, 2, 3*(2*k+1)+1, 2*(2*k+1)+1, 0)
theorem main_trans (k : ℕ) :
    ⟨(0 : ℕ), 0, 2, 3 * k + 1, 2 * k + 1, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2, 3 * (2 * k + 1) + 1, 2 * (2 * k + 1) + 1, 0⟩ := by
  -- Phase 1: consume c=2, go to (0, 0, 0, 3*k+1, 2*k+1, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3 * k + 1, 2 * k + 1, 0⟩)
  · exact phase1 (3 * k) (2 * k + 1)
  -- Phase 2: R4 loop: (0, 0, 0, 3*k+1, 2*k+1, 0) → (0, 3*k+1, 0, 0, 2*k+1, 3*k+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3 * k + 1, 0, 0, 2 * k + 1, 3 * k + 1⟩)
  · have h := r4_loop (3 * k + 1) 0 0 (2 * k + 1) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5-R1-R1 loop: (0, 3*k+1, 0, 0, 2*k+1, 3*k+1) → (2, 0, 0, 0, k, 3*k+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 0, 0, 0, k, 3 * k + 1⟩)
  · have h := r5r1r1_loop k k (3 * k + 1)
    rw [show k + 1 + k = 2 * k + 1 from by ring] at h
    exact h
  -- Phase 4: 2 R2 steps: (2, 0, 0, 0, k, 3*k+1) → (0, 0, 2, 2, k+2, 3*k+1)
  step fm  -- R2: (1, 0, 1, 1, k+1, 3*k+1)
  step fm  -- R2: (0, 0, 2, 2, k+2, 3*k+1)
  -- Phase 5: R3-R2 loop: (0, 0, 2, 2, k+2, 3*k+1) → (0, 0, 2, 2+2*(3*k+1), k+2+(3*k+1), 0)
  apply stepStar_trans (c₂ := ⟨0, 0, 2, 2 + 2 * (3 * k + 1), (k + 2) + (3 * k + 1), 0⟩)
  · have h := r3r2_loop (3 * k + 1) 2 (k + 2) 0
    simp only [Nat.zero_add] at h; exact h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 3 * 1 + 1, 2 * 1 + 1, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun k ↦ ⟨0, 0, 2, 3 * k + 1, 2 * k + 1, 0⟩) 1
  intro k; exact ⟨2 * k + 1, main_trans k⟩

end Sz22_2003_unofficial_206
