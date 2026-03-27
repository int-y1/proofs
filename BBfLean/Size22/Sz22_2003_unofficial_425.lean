import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #425: [27/10, 55/21, 22/3, 7/11, 9/2]

Vector representation:
```
-1  3 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  1
 0  0  0  1 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_425

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- Alternating R2, R1: consume a and d, grow b and e
theorem r2r1_chain : ∀ j, ∀ a b d e,
    ⟨a+j, b+2, 0, d+j, e⟩ [fm]⊢* ⟨a, b+2+2*j, 0, d, e+j⟩ := by
  intro j; induction' j with j ih <;> intro a b d e
  · exists 0
  rw [show a + (j + 1) = (a + j) + 1 from by ring,
      show d + (j + 1) = (d + j) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  rw [show b + 2 + 2 + 2 * j = b + 2 + 2 * (j + 1) from by ring,
      show e + 1 + j = e + (j + 1) from by ring]
  finish

-- R2 chain: consume b and d, produce c and e
theorem r2_chain : ∀ j, ∀ b c d e,
    ⟨0, b+j, c, d+j, e⟩ [fm]⊢* ⟨0, b, c+j, d, e+j⟩ := by
  intro j; induction' j with j ih <;> intro b c d e
  · exists 0
  rw [show b + (j + 1) = (b + j) + 1 from by ring,
      show d + (j + 1) = (d + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _ _)
  rw [show c + 1 + j = c + (j + 1) from by ring,
      show e + 1 + j = e + (j + 1) from by ring]
  finish

-- Alternating R3, R1: consume c, grow b and e
theorem r3r1_chain : ∀ j, ∀ b e,
    ⟨0, b+1, j, 0, e⟩ [fm]⊢* ⟨0, b+1+2*j, 0, 0, e+j⟩ := by
  intro j; induction' j with j ih <;> intro b e
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih _ _)
  rw [show b + 2 + 1 + 2 * j = b + 1 + 2 * (j + 1) from by ring,
      show e + 1 + j = e + (j + 1) from by ring]
  finish

-- R3 chain: convert b to a and e
theorem r3_chain : ∀ j, ∀ a e,
    ⟨a, j, 0, 0, e⟩ [fm]⊢* ⟨a+j, 0, 0, 0, e+j⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  rw [show a + 1 + j = a + (j + 1) from by ring,
      show e + 1 + j = e + (j + 1) from by ring]
  finish

-- R4 chain: convert e to d
theorem r4_chain : ∀ j, ∀ a d,
    ⟨a, 0, 0, d, j⟩ [fm]⊢* ⟨a, 0, 0, d+j, 0⟩ := by
  intro j; induction' j with j ih <;> intro a d
  · exists 0
  step fm
  apply stepStar_trans (ih _ _)
  rw [show d + 1 + j = d + (j + 1) from by ring]
  finish

-- Main transition: (n+2, 0, 0, 2n+2, 0) ⊢⁺ (3n+5, 0, 0, 6n+8, 0)
theorem main_trans (n : ℕ) :
    ⟨n+2, 0, 0, 2*n+2, 0⟩ [fm]⊢⁺ ⟨3*n+5, 0, 0, 6*n+8, 0⟩ := by
  -- Phase 1a: R5
  apply step_stepStar_stepPlus
  · show fm ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ = some ⟨n + 1, 2, 0, 2 * n + 2, 0⟩; rfl
  -- Phase 1b: R2R1 chain (n+1 times)
  apply stepStar_trans
  · show ⟨n + 1, 2, 0, 2 * n + 2, 0⟩ [fm]⊢* ⟨0, 2 * n + 4, 0, n + 1, n + 1⟩
    have h := r2r1_chain (n+1) 0 0 (n+1) 0
    simp only [(by ring : 0 + 2 = 2),
               (by ring : (n + 1) + (n + 1) = 2 * n + 2),
               (by ring : 0 + 2 + 2 * (n + 1) = 2 * n + 4),
               (by ring : 0 + (n + 1) = n + 1)] at h
    exact h
  -- Phase 2: R2 chain (n+1 times)
  apply stepStar_trans
  · show ⟨0, 2 * n + 4, 0, n + 1, n + 1⟩ [fm]⊢* ⟨0, n + 3, n + 1, 0, 2 * n + 2⟩
    have h := r2_chain (n+1) (n+3) 0 0 (n+1)
    simp only [(by ring : (n + 3) + (n + 1) = 2 * n + 4),
               (by ring : 0 + (n + 1) = n + 1),
               (by ring : (n + 1) + (n + 1) = 2 * n + 2)] at h
    exact h
  -- Phase 3: R3R1 chain (n+1 times)
  apply stepStar_trans
  · show ⟨0, n + 3, n + 1, 0, 2 * n + 2⟩ [fm]⊢* ⟨0, 3 * n + 5, 0, 0, 3 * n + 3⟩
    have h := r3r1_chain (n+1) (n+2) (2*n+2)
    simp only [(by ring : (n + 2) + 1 = n + 3),
               (by ring : (n + 2) + 1 + 2 * (n + 1) = 3 * n + 5),
               (by ring : (2 * n + 2) + (n + 1) = 3 * n + 3)] at h
    exact h
  -- Phase 4: R3 chain
  apply stepStar_trans
  · show ⟨0, 3 * n + 5, 0, 0, 3 * n + 3⟩ [fm]⊢* ⟨3 * n + 5, 0, 0, 0, 6 * n + 8⟩
    have h := r3_chain (3*n+5) 0 (3*n+3)
    simp only [(by ring : 0 + (3 * n + 5) = 3 * n + 5),
               (by ring : (3 * n + 3) + (3 * n + 5) = 6 * n + 8)] at h
    exact h
  -- Phase 5: R4 chain
  show ⟨3 * n + 5, 0, 0, 0, 6 * n + 8⟩ [fm]⊢* ⟨3 * n + 5, 0, 0, 6 * n + 8, 0⟩
  have h := r4_chain (6*n+8) (3*n+5) 0
  simp only [(by ring : 0 + (6 * n + 8) = 6 * n + 8)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*n+2, 0⟩) 0
  intro n
  refine ⟨3*n+3, ?_⟩
  show ⟨n + 2, 0, 0, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨3 * n + 3 + 2, 0, 0, 2 * (3 * n + 3) + 2, 0⟩
  rw [show 3 * n + 3 + 2 = 3 * n + 5 from by ring,
      show 2 * (3 * n + 3) + 2 = 6 * n + 8 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_425
