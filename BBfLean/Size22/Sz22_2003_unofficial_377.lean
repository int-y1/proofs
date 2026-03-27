import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #377: [2/15, 99/14, 125/2, 7/11, 14/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  3  0  0
 0  0  0  1 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_377

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to d
theorem e_to_d : ∀ j c d e,
    ⟨0, 0, c, d, e+j⟩ [fm]⊢* ⟨0, 0, c, d+j, e⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show e + (j + 1) = (e + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5,R2,R1,R1: (0, 0, c+3, d, 0) -> (2, 0, c, d, 1)
theorem r5_r2_r1_r1 : ∀ c d,
    ⟨0, 0, c+3, d, 0⟩ [fm]⊢⁺ ⟨2, 0, c, d, 1⟩ := by
  intro c d
  step fm; step fm; step fm; step fm; finish

-- One round of R2,R1,R1: (a+1, 0, c+2, d+1, e) -> (a+2, 0, c, d, e+1)
theorem r2_r1_r1 : ∀ a c d e,
    ⟨a+1, 0, c+2, d+1, e⟩ [fm]⊢* ⟨a+2, 0, c, d, e+1⟩ := by
  intro a c d e
  step fm; step fm; step fm; finish

-- Iterate R2,R1,R1 j times
theorem r2_r1_r1_iter : ∀ j a c d e,
    ⟨a+1, 0, c+2*j, d+j, e⟩ [fm]⊢* ⟨a+1+j, 0, c, d, e+j⟩ := by
  intro j; induction' j with j ih <;> intro a c d e
  · exists 0
  rw [show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring,
      show d + (j + 1) = (d + j) + 1 from by ring]
  apply stepStar_trans (r2_r1_r1 _ _ _ _)
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R3 chain: transfer a to c (multiplied by 3)
theorem a_to_c : ∀ j a c e,
    ⟨a+j, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+3*j, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro a c e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: (0, 0, c + 2*e + 3, 0, e) ⊢⁺ (0, 0, c + 3*e + 6, 0, e + 1)
theorem main_trans (c e : ℕ) :
    ⟨0, 0, c + 2*e + 3, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + 3*e + 6, 0, e + 1⟩ := by
  -- Phase 1: R4 x e: transfer e to d
  -- (0, 0, c+2e+3, 0, e) ->* (0, 0, c+2e+3, e, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := e_to_d e (c + 2*e + 3) 0 0
    simp only [(by ring : 0 + e = e)] at h
    exact h
  -- Phase 2: R5,R2,R1,R1
  -- (0, 0, c+2e+3, e, 0) ->⁺ (2, 0, c+2e, e, 1)
  apply stepPlus_stepStar_stepPlus
  · have h := r5_r2_r1_r1 (c + 2*e) e
    rw [show c + 2 * e + 3 = (c + 2 * e) + 3 from by ring] at h
    exact h
  -- Phase 3: R2,R1,R1 x e times
  -- (2, 0, c+2e, e, 1) ->* (e+2, 0, c, 0, e+1)
  apply stepStar_trans
  · have h := r2_r1_r1_iter e 1 c 0 1
    rw [show (1 : ℕ) + 1 = 2 from rfl,
        show (0 : ℕ) + e = e from Nat.zero_add e,
        show (1 : ℕ) + 1 + e = e + 2 from by ring,
        show (1 : ℕ) + e = e + 1 from by ring] at h
    exact h
  -- Phase 4: R3 x (e+2)
  -- (e+2, 0, c, 0, e+1) ->* (0, 0, c+3*(e+2), 0, e+1)
  have h := a_to_c (e + 2) 0 c (e + 1)
  rw [show (0 : ℕ) + (e + 2) = e + 2 from Nat.zero_add (e + 2),
      show c + 3 * (e + 2) = c + 3 * e + 6 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, e⟩ ↦ ⟨0, 0, c + 2*e + 3, 0, e⟩) ⟨0, 0⟩
  intro ⟨c, e⟩
  refine ⟨⟨c + e + 1, e + 1⟩, ?_⟩
  show ⟨0, 0, c + 2 * e + 3, 0, e⟩ [fm]⊢⁺ ⟨0, 0, (c + e + 1) + 2 * (e + 1) + 3, 0, e + 1⟩
  rw [show (c + e + 1) + 2 * (e + 1) + 3 = c + 3 * e + 6 from by ring]
  exact main_trans c e

end Sz22_2003_unofficial_377
