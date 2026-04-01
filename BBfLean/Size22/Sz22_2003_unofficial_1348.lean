import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1348: [63/10, 35/33, 4/3, 11/7, 15/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  1 -1
 2 -1  0  0  0
 0  0  0 -1  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1348

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: move d to e
theorem d_to_e : ∀ k, ∀ d e, ⟨a, (0 : ℕ), 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- R1R2 pair: one round of R1 then R2
-- (A+1, b, 1, D, E+1) → (A, b+2, 0, D+1, E+1) → (A, b+1, 1, D+2, E)
theorem r1r2_pair : ∀ A b D E, ⟨A + 1, b, (1 : ℕ), D, E + 1⟩ [fm]⊢* ⟨A, b + 1, 1, D + 2, E⟩ := by
  intro A b D E
  step fm
  step fm
  finish

-- R1R2 chain: k rounds
theorem r1r2_chain : ∀ k, ∀ A b D, ⟨A + k, b, (1 : ℕ), D, k⟩ [fm]⊢* ⟨A, b + k, 1, D + 2 * k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro A b D
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show (k + 1) = k + 1 from rfl]
    apply stepStar_trans (r1r2_pair (A + k) b D k)
    apply stepStar_trans (ih A (b + 1) (D + 2))
    ring_nf; finish

-- R3 chain: drain b
theorem b_drain : ∀ k, ∀ A d, ⟨A, k, (0 : ℕ), d, (0 : ℕ)⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro A d
  · exists 0
  · rw [show (k + 1) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (A + 2) d)
    ring_nf; finish

-- Main transition: (x+D+3, 0, 0, D+1, 0) →⁺ (x+2D+8, 0, 0, 2D+3, 0)
theorem main_trans (x D : ℕ) :
    ⟨x + D + 3, (0 : ℕ), 0, D + 1, 0⟩ [fm]⊢⁺
    ⟨x + 2 * D + 8, (0 : ℕ), 0, 2 * D + 3, 0⟩ := by
  -- Phase 1: R4 chain, move D+1 from d to e
  rw [show D + 1 = 0 + (D + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (a := x + D + 3) (D + 1) 0 0)
  rw [show (0 : ℕ) + (D + 1) = D + 1 from by ring]
  -- State: (x+D+3, 0, 0, 0, D+1)
  -- Phase 2: R5
  rw [show x + D + 3 = (x + D + 2) + 1 from by ring,
      show D + 1 = (D + 1) from rfl]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨(x + D + 2) + 1, (0 : ℕ), 0, 0, D + 1⟩ : Q) [fm]⊢ ⟨x + D + 2, 1, 1, 0, D + 1⟩)
  -- State: (x+D+2, 1, 1, 0, D+1)
  -- Phase 3: R1R2 chain, D+1 rounds
  rw [show x + D + 2 = (x + 1) + (D + 1) from by ring]
  apply stepStar_trans (r1r2_chain (D + 1) (x + 1) 1 0)
  rw [show 1 + (D + 1) = D + 2 from by ring,
      show 0 + 2 * (D + 1) = 2 * D + 2 from by ring]
  -- State: (x+1, D+2, 1, 2D+2, 0)
  -- Phase 4: R1 (a = x+1 >= 1, c = 1 >= 1)
  rw [show x + 1 = x + 1 from rfl,
      show D + 2 = (D + 1) + 1 from by ring]
  step fm
  -- State: (x, D+4, 0, 2D+3, 0)
  rw [show D + 1 + 2 + 1 = D + 4 from by ring]
  -- Phase 5: R3 chain, drain b = D+4
  apply stepStar_trans (b_drain (D + 4) x (2 * D + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨x, D⟩ ↦ ⟨x + D + 3, 0, 0, D + 1, 0⟩) ⟨2, 0⟩
  intro ⟨x, D⟩
  refine ⟨⟨x + 3, 2 * D + 2⟩, ?_⟩
  show ⟨x + D + 3, (0 : ℕ), 0, D + 1, 0⟩ [fm]⊢⁺
    ⟨(x + 3) + (2 * D + 2) + 3, 0, 0, (2 * D + 2) + 1, 0⟩
  rw [show (x + 3) + (2 * D + 2) + 3 = x + 2 * D + 8 from by ring,
      show (2 * D + 2) + 1 = 2 * D + 3 from by ring]
  exact main_trans x D

end Sz22_2003_unofficial_1348
