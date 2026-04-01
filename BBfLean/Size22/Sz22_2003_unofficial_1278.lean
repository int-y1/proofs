import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1278: [56/15, 1/6, 9/7, 25/2, 6/5]

Vector representation:
```
 3 -1 -1  1
-1 -1  0  0
 0  2  0 -1
-1  0  2  0
 1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1278

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+3, b, c, d+1⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b+1, c, d⟩
  | _ => none

-- R4 drain: each step converts 1 from a to 2 in c.
theorem r4_drain : ∀ k c, ⟨k, 0, c, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [show k + 1 = (k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2))
    ring_nf; finish

-- R3R1R1 chain: each round fires R1,R1,R3 consuming 2 from c.
theorem r3r1r1_chain : ∀ k A C D, ⟨A, 2, C + 2 * k, D⟩ [fm]⊢* ⟨A + 6 * k, 2, C, D + k⟩ := by
  intro k; induction' k with k ih <;> intro A C D
  · exists 0
  · rw [show C + 2 * (k + 1) = (C + 2 * k) + 2 from by ring]
    step fm; step fm
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A + 6) C (D + 1))
    ring_nf; finish

-- R2R2R3 drain: each round fires R2,R2,R3 reducing a and d.
theorem r2r2r3_drain : ∀ k A, ⟨A + 2 * k, 2, 0, k⟩ [fm]⊢* ⟨A, 2, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A
  · exists 0
  · rw [show A + 2 * (k + 1) = (A + 2 * k) + 1 + 1 from by ring]
    step fm; step fm
    rw [show k + 1 = k + 1 from rfl]
    step fm
    exact ih A

-- Main transition: (2*n+2, 0, 0, 0) ⊢⁺ (8*n+6, 0, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨2 * n + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨8 * n + 6, 0, 0, 0⟩ := by
  -- Phase 1: R4 drain
  have phase1 : ⟨2 * n + 2, 0, 0, 0⟩ [fm]⊢* ⟨0, 0, 4 * n + 4, 0⟩ := by
    have := r4_drain (2 * n + 2) 0
    simp at this; rw [show 2 * (2 * n + 2) = 4 * n + 4 from by ring] at this; exact this
  -- Phase 2: R5 + R1
  have phase2 : ⟨0, 0, 4 * n + 4, 0⟩ [fm]⊢⁺ ⟨4, 0, 4 * n + 2, 1⟩ := by
    rw [show 4 * n + 4 = (4 * n + 3) + 1 from by ring]
    step fm
    rw [show 4 * n + 3 = (4 * n + 2) + 1 from by ring]
    step fm; finish
  -- Phase 3: R3 (one step to get b=2)
  have phase3 : ⟨4, 0, 4 * n + 2, 1⟩ [fm]⊢⁺ ⟨4, 2, 4 * n + 2, 0⟩ := by
    step fm; finish
  -- Phase 4: R3R1R1 chain (2*n+1 rounds)
  have phase4 : ⟨4, 2, 4 * n + 2, 0⟩ [fm]⊢* ⟨12 * n + 10, 2, 0, 2 * n + 1⟩ := by
    have := r3r1r1_chain (2 * n + 1) 4 0 0
    rw [show 0 + 2 * (2 * n + 1) = 4 * n + 2 from by ring,
        show 4 + 6 * (2 * n + 1) = 12 * n + 10 from by ring,
        show 0 + (2 * n + 1) = 2 * n + 1 from by ring] at this
    exact this
  -- Phase 5: R2R2R3 drain (2*n+1 rounds)
  have phase5 : ⟨12 * n + 10, 2, 0, 2 * n + 1⟩ [fm]⊢* ⟨8 * n + 8, 2, 0, 0⟩ := by
    have := r2r2r3_drain (2 * n + 1) (8 * n + 8)
    rw [show 8 * n + 8 + 2 * (2 * n + 1) = 12 * n + 10 from by ring] at this
    exact this
  -- Phase 6: R2, R2
  have phase6 : ⟨8 * n + 8, 2, 0, 0⟩ [fm]⊢⁺ ⟨8 * n + 6, 0, 0, 0⟩ := by
    rw [show 8 * n + 8 = (8 * n + 6) + 1 + 1 from by ring]
    step fm; step fm; finish
  exact stepStar_stepPlus_stepPlus phase1
    (stepPlus_trans phase2
      (stepPlus_trans phase3
        (stepStar_stepPlus_stepPlus phase4
          (stepStar_stepPlus_stepPlus phase5 phase6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 2, 0, 0, 0⟩) 0
  intro n; exact ⟨4 * n + 2, by rw [show 2 * (4 * n + 2) + 2 = 8 * n + 6 from by ring]; exact main_trans n⟩

end Sz22_2003_unofficial_1278
