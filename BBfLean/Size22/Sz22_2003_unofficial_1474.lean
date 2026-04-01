import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1474: [7/15, 4/3, 1089/14, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0  0
-1  2  0 -1  2
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1474

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4: transfer e to c (with b=0, d=0).
theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c := c + 1) (e := e)); ring_nf; finish

-- R1R1R3 chain: each round drains c by 2, increments d, adds 2 to e.
theorem r1r1r3_chain : ∀ k, ∀ A D E, ⟨A + k, 2, 2 * k, D, E⟩ [fm]⊢* ⟨A, 2, 0, D + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro A D E; exists 0
  · intro A D E
    rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm
    rw [show (2 * k + 1) = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih A (D + 1) (E + 2)); ring_nf; finish

-- R2R2R3 chain: drains d, each round adds 3 to a and 2 to e.
theorem r2r2r3_chain : ∀ k, ∀ A E, ⟨A, 2, 0, k, E⟩ [fm]⊢* ⟨A + 3 * k, 2, 0, 0, E + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro A E; exists 0
  · intro A E
    rw [show (k + 1) = k + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 3) (E + 2)); ring_nf; finish

-- Main transition: (2n+2, 0, 0, 0, 2n+1) ⊢⁺ (4n+4, 0, 0, 0, 4n+3).
theorem main_trans (n : ℕ) :
    ⟨2 * n + 2, 0, 0, 0, 2 * n + 1⟩ [fm]⊢⁺ ⟨4 * n + 4, 0, 0, 0, 4 * n + 3⟩ := by
  -- Phase 1: R4 chain, transfer e to c.
  rw [show (2 * n + 1 : ℕ) = 0 + (2 * n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * n + 1) (a := 2 * n + 2) (c := 0) (e := 0))
  rw [show (0 : ℕ) + (2 * n + 1) = 2 * n + 1 from by ring]
  -- Phase 2: R5 step.
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  -- Phase 3: R1 step.
  rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
  step fm
  -- Phase 4: R3 step.
  step fm
  -- Phase 5: R1R1R3 chain (n rounds).
  have h5 := r1r1r3_chain n n 0 3
  rw [show n + n = 2 * n from by ring,
      show 0 + n = n from by ring,
      show 3 + 2 * n = 2 * n + 3 from by ring] at h5
  apply stepStar_trans h5
  -- Phase 6: R2R2R3 chain (n rounds).
  have h6 := r2r2r3_chain n n (2 * n + 3)
  rw [show n + 3 * n = 4 * n from by ring,
      show 2 * n + 3 + 2 * n = 4 * n + 3 from by ring] at h6
  apply stepStar_trans h6
  -- Phase 7: Final R2R2.
  step fm; step fm; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 2, 0, 0, 0, 2 * n + 1⟩) 0
  intro n; refine ⟨2 * n + 1, ?_⟩
  have h := main_trans n
  rw [show 4 * n + 4 = 2 * (2 * n + 1) + 2 from by ring,
      show 4 * n + 3 = 2 * (2 * n + 1) + 1 from by ring] at h
  exact h

end Sz22_2003_unofficial_1474
