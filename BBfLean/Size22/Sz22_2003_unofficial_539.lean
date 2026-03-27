import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #539: [28/15, 9/22, 25/2, 121/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  2  0  0 -1
-1  0  2  0  0
 0  0  0 -1  2
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_539

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R3 repeated, converting a to c
theorem a_to_c : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2*k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show k + 1 = (k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 2: R4 repeated, converting d to e
theorem d_to_e : ∀ k c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + 2*k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 3: Opening two steps R5, R1
theorem opening : ⟨0, 0, c + 2, 0, e + 1⟩ [fm]⊢* ⟨2, 0, c, 1, e + 1⟩ := by
  step fm; step fm; finish

-- Phase 4: Interleaved (R2, R1, R1) chain
theorem r2r1r1_chain : ∀ k, ∀ A D E, ⟨A + 1, 0, 2*k, D, E + k⟩ [fm]⊢* ⟨A + 1 + 3*k, 0, 0, D + 2*k, E⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 5: R2 chain, converting e to b
theorem r2_chain : ∀ k, ∀ A b D, ⟨A + k, b, 0, D, k⟩ [fm]⊢* ⟨A, b + 2*k, 0, D, 0⟩ := by
  intro k; induction' k with k ih <;> intro A b D
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 6: (R3, R1, R1) chain, converting b to a and d
theorem r3r1r1_chain : ∀ k, ∀ A D, ⟨A + 1, 2*k, 0, D, 0⟩ [fm]⊢* ⟨A + 1 + 3*k, 0, 0, D + 2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Main transition
theorem main_trans (m d : ℕ) (hd : d ≥ 1) (hm : m ≤ d) :
    ⟨m + d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨m + 5*d + 2, 0, 0, 4*d + 1, 0⟩ := by
  -- First step via R3 to establish ⊢⁺
  rw [show m + d + 1 = (m + d) + 1 from by ring]
  step fm
  -- Now we have (m+d, 0, 2, d, 0) and need ⊢* to the target
  -- Remaining R3 steps
  apply stepStar_trans (a_to_c (m+d) 2 d)
  rw [show 2 + 2 * (m + d) = 2*m + 2*d + 2 from by ring]
  -- Phase 2: R4 chain
  apply stepStar_trans (d_to_e d (2*m + 2*d + 2) 0)
  rw [show 0 + 2 * d = 2*d from by ring]
  -- Phase 3: opening
  rw [show 2*m + 2*d + 2 = (2*(m+d)) + 2 from by ring,
      show 2*d = ((d - m) + (m+d) - 1) + 1 from by omega]
  apply stepStar_trans opening
  -- Phase 4: r2r1r1 chain with k=m+d rounds
  rw [show (d - m + (m + d) - 1 + 1 : ℕ) = (d - m) + (m + d) from by omega]
  apply stepStar_trans (r2r1r1_chain (m+d) 1 1 (d-m))
  -- Phase 5: r2 chain
  rw [show 1 + 1 + 3 * (m + d) = (4*m + 2*d + 2) + (d - m) from by omega,
      show 1 + 2 * (m + d) = 2*m + 2*d + 1 from by ring]
  apply stepStar_trans (r2_chain (d-m) (4*m+2*d+2) 0 (2*m+2*d+1))
  rw [show 0 + 2 * (d - m) = 2*(d-m) from by ring]
  -- Phase 6: r3r1r1 chain
  rw [show (4*m + 2*d + 2 : ℕ) = (4*m + 2*d + 1) + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain (d-m) (4*m+2*d+1) (2*m+2*d+1))
  rw [show 4*m + 2*d + 1 + 1 + 3*(d-m) = m + 5*d + 2 from by omega,
      show 2*m + 2*d + 1 + 2*(d-m) = 4*d + 1 from by omega]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m d, q = ⟨m + d + 1, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ m ≤ d)
  · intro c ⟨m, d, hq, hd, hm⟩; subst hq
    refine ⟨⟨m + 5*d + 2, 0, 0, 4*d + 1, 0⟩,
           ⟨m + d, 4*d + 1, ?_, by omega, by omega⟩,
           main_trans m d hd hm⟩
    congr 1; omega
  · exact ⟨0, 1, rfl, by omega, by omega⟩
