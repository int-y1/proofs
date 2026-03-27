import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #553: [308/15, 1/3, 3/7, 25/2, 1/55, 3/5]

Vector representation:
```
 2 -1 -1  1  1
 0 -1  0  0  0
 0  1  0 -1  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_553

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1+R3 chain: each round does R1 (b=1,c≥1) then R3 (d=1)
theorem r1r3_chain : ∀ k, ∀ a e, ⟨a, (1 : ℕ), k, (0 : ℕ), e⟩ [fm]⊢* ⟨a + 2*k, 1, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show (k : ℕ) + 1 = k + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R4 chain: convert a to c
theorem a_to_c : ∀ a, ∀ c, ⟨a, (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢* ⟨0, 0, c + 2*a, 0, e⟩ := by
  intro a; induction' a with a ih <;> intro c
  · exists 0
  step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

-- R5 chain: cancel c and e
theorem r5_chain : ∀ k, ∀ c, ⟨(0 : ℕ), (0 : ℕ), c + k, (0 : ℕ), k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega]
  rw [show (k : ℕ) + 1 = k + 1 from rfl]
  step fm
  exact ih c

-- Main transition: (0, 0, c+2, 0, 0) →⁺ (0, 0, 3c+3, 0, 0)
theorem main_trans : ⟨(0 : ℕ), (0 : ℕ), c + 2, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺
    ⟨0, 0, 3*c + 3, 0, 0⟩ := by
  -- R6: (0, 0, c+2, 0, 0) → (0, 1, c+1, 0, 0)
  step fm
  -- R1+R3 chain: (0, 1, c+1, 0, 0) →* (2*(c+1), 1, 0, 0, c+1)
  apply stepStar_trans (r1r3_chain (c + 1) 0 0)
  simp only [Nat.zero_add]
  -- R2: (2*(c+1), 1, 0, 0, c+1) → (2*(c+1), 0, 0, 0, c+1)
  apply stepStar_trans (step_stepStar (by unfold fm; rfl))
  -- R4 chain: (2*(c+1), 0, 0, 0, c+1) →* (0, 0, 4*(c+1), 0, c+1)
  apply stepStar_trans (a_to_c (2 * (c + 1)) 0)
  -- R5 chain
  rw [show 0 + 2 * (2 * (c + 1)) = 3 * (c + 1) + (c + 1) from by ring]
  apply stepStar_trans (r5_chain (c + 1) (3 * (c + 1)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun c ↦ ⟨0, 0, c + 2, 0, 0⟩) 0
  intro c; exact ⟨3 * c + 1, by
    rw [show 3 * c + 1 + 2 = 3 * c + 3 from by omega]
    exact main_trans⟩
