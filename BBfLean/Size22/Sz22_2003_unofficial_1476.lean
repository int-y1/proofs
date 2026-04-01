import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1476: [7/15, 4/3, 99/14, 25/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0  0
-1  2  0 -1  1
 0  0  2  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1476

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Phase 1b: R3, R1, R1 loop × k iterations.
-- (A+k, 0, 2*k+1, K+1, K+1) ⊢* (A, 0, 1, K+k+1, K+k+1)
theorem phase1_loop : ∀ k A K,
    ⟨A + k, 0, 2 * k + 1, K + 1, K + 1⟩ [fm]⊢*
    ⟨A, 0, 1, K + k + 1, K + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A K
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A (K + 1)); ring_nf; finish

-- Phase 2: R3, R2, R2 chain × k iterations.
-- (A+1, 0, 0, k, E) ⊢* (A+3*k+1, 0, 0, 0, E+k)
theorem phase2_chain : ∀ k A E,
    ⟨A + 1, 0, 0, k, E⟩ [fm]⊢* ⟨A + 3 * k + 1, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · rw [show A + 1 = (A + 0) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 3) (E + 1)); ring_nf; finish

-- Phase 3: R4 chain, transfer e to c.
-- (A, 0, C, 0, k) ⊢* (A, 0, C+2*k, 0, 0)
theorem phase3_e_to_c : ∀ k A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm
    apply stepStar_trans (ih A (C + 2)); ring_nf; finish

-- Main transition: canonical state (F+n+2, 0, 2*(n+1), 0, 0) advances to
-- ((F+n+1)+(2*n+2)+2, 0, 2*((2*n+2)+1), 0, 0) = (F+3*n+5, 0, 4*n+6, 0, 0).
theorem main_trans (F n : ℕ) :
    ⟨F + n + 2, 0, 2 * (n + 1), 0, 0⟩ [fm]⊢⁺
    ⟨F + 3 * n + 5, 0, 4 * n + 6, 0, 0⟩ := by
  -- Phase 1a: opening R5, R1
  rw [show F + n + 2 = (F + n + 1) + 1 from by ring,
      show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  step fm; step fm
  -- State: (F+n+1, 0, 2*n+1, 1, 1). Need (F+1)+n = F+n+1.
  rw [show F + n + 1 = (F + 1) + n from by ring]
  -- Phase 1b: R3, R1, R1 loop × n
  apply stepStar_trans (phase1_loop n (F + 1) 0)
  -- State: (F+1, 0, 1, n+1, n+1)
  -- Phase 1c: finish R3, R1, R2
  rw [show F + 1 = F + 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm
  -- State: (F+2, 0, 0, n+1, n+2)
  rw [show 0 + n + 1 + 1 = n + 2 from by ring,
      show 0 + n + 1 = n + 1 from by ring,
      show F + 0 + 2 = (F + 1) + 1 from by ring]
  -- Phase 2: R3, R2, R2 × (n+1)
  apply stepStar_trans (phase2_chain (n + 1) (F + 1) (n + 2))
  -- State: (F+1+3*(n+1)+1, 0, 0, 0, (n+2)+(n+1)) = (F+3*n+5, 0, 0, 0, 2*n+3)
  rw [show F + 1 + 3 * (n + 1) + 1 = F + 3 * n + 5 from by ring,
      show n + 2 + (n + 1) = 2 * n + 3 from by ring]
  -- Phase 3: R4 × (2*n+3)
  apply stepStar_trans (phase3_e_to_c (2 * n + 3) (F + 3 * n + 5) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, n⟩ ↦ ⟨F + n + 2, 0, 2 * (n + 1), 0, 0⟩) ⟨0, 0⟩
  intro ⟨F, n⟩
  refine ⟨⟨F + n + 1, 2 * n + 2⟩, ?_⟩
  show ⟨F + n + 2, 0, 2 * (n + 1), 0, 0⟩ [fm]⊢⁺
       ⟨F + n + 1 + (2 * n + 2) + 2, 0, 2 * (2 * n + 2 + 1), 0, 0⟩
  rw [show F + n + 1 + (2 * n + 2) + 2 = F + 3 * n + 5 from by ring,
      show 2 * (2 * n + 2 + 1) = 4 * n + 6 from by ring]
  exact main_trans F n

end Sz22_2003_unofficial_1476
