import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #778: [35/6, 55/2, 52/77, 3/13, 21/5]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  1  0  1  0
 2  0  0 -1 -1  1
 0  1  0  0  0 -1
 0  1 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_778

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: move f to b (when a=0, d=0).
theorem f_to_b : ∀ k b c e f, ⟨0, b, c, 0, e, k + f⟩ [fm]⊢* ⟨0, b + k, c, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c e f
  · simp; finish
  · rw [show k + 1 + f = k + (f + 1) from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R3,R1,R1 chain repeated k times.
theorem r3r1r1_chain : ∀ k b c d e f,
    ⟨0, b + 2 * k, c, d + 1, e + k, f⟩ [fm]⊢*
    ⟨0, b, c + 2 * k, d + k + 1, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · simp; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih _ (c + 2) (d + 1) _ (f + 1))
    ring_nf; finish

-- R3,R2,R2 chain repeated k times.
theorem r3r2r2_chain : ∀ k c d e f,
    ⟨0, 0, c, d + k, e + 1, f⟩ [fm]⊢*
    ⟨0, 0, c + 2 * k, d, e + k + 1, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · simp; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 1 + 1 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih (c + 2) _ (e + 1) (f + 1))
    ring_nf; finish

-- Full transition from one canonical state to the next.
theorem main_transition (n : ℕ) :
    ⟨0, 0, 2 * n ^ 2 + 5 * n + 4, 0, n + 2, 2 * n + 2⟩ [fm]⊢⁺
    ⟨0, 0, 2 * (n + 1) ^ 2 + 5 * (n + 1) + 4, 0, (n + 1) + 2, 2 * (n + 1) + 2⟩ := by
  -- Phase 1: R4 drain f to b
  rw [show (2 * n + 2 : ℕ) = (2 * n + 2) + 0 from by ring]
  apply stepStar_stepPlus_stepPlus (f_to_b (2 * n + 2) 0 (2 * n ^ 2 + 5 * n + 4) (n + 2) 0)
  simp
  -- State: (0, 2n+2, 2n^2+5n+4, 0, n+2, 0)
  -- Phase 2: R5
  rw [show 2 * n ^ 2 + 5 * n + 4 = (2 * n ^ 2 + 5 * n + 3) + 1 from by ring]
  step fm
  -- State: (0, 2n+3, 2n^2+5n+3, 1, n+2, 0)
  rw [show 2 * n + 2 + 1 = 1 + 2 * (n + 1) from by ring,
      show n + 2 = 1 + (n + 1) from by ring]
  -- Phase 3: R3,R1,R1 chain (n+1 rounds)
  apply stepStar_trans (r3r1r1_chain (n + 1) 1 (2 * n ^ 2 + 5 * n + 3) 0 1 0)
  rw [show 2 * n ^ 2 + 5 * n + 3 + 2 * (n + 1) = 2 * n ^ 2 + 7 * n + 5 from by ring,
      show 0 + (n + 1) + 1 = n + 2 from by ring,
      show 0 + (n + 1) = n + 1 from by ring]
  -- State: (0, 1, 2n^2+7n+5, n+2, 1, n+1)
  -- Phase 4: R3,R1,R2 bridge
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm  -- R3
  step fm  -- R1
  step fm  -- R2
  rw [show 2 * n ^ 2 + 7 * n + 5 + 1 + 1 = 2 * n ^ 2 + 7 * n + 7 from by ring,
      show n + 1 + 1 = n + 2 from by ring]
  -- State: (0, 0, 2n^2+7n+7, n+2, 1, n+2)
  -- Phase 5: R3,R2,R2 chain (n+2 rounds)
  rw [show n + 2 = 0 + (n + 2) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (n + 2) (2 * n ^ 2 + 7 * n + 7) 0 0 (0 + (n + 2)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 2, 2⟩) (by execute fm 8)
  have := progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n ^ 2 + 5 * n + 4, 0, n + 2, 2 * n + 2⟩) 0
    (fun n ↦ ⟨n + 1, main_transition n⟩)
  exact this
