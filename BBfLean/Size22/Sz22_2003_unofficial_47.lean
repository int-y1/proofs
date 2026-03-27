import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #47: [1/15, 686/3, 3/77, 5/49, 363/2]

Vector representation:
```
 0 -1 -1  0  0
 1 -1  0  3  0
 0  1  0 -1 -1
 0  0  1 -2  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_47

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+3, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R2/R1 chain: each round consumes 1 from e, adds 1 to a and 2 to d
theorem r2r1_chain : ∀ k, ∀ a d e,
    ⟨a, 0, 0, d + 1, e + k⟩ [fm]⊢* ⟨a + k, 0, 0, d + 1 + 2 * k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h (a + 1) (d + 2) e)
  ring_nf; finish

-- R3 chain: d → c (d decreases by 2, c increases by 1 each step)
theorem r3_chain : ∀ k, ∀ a c d,
    ⟨a, 0, c, d + 2 * k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (h a (c + 1) d)
  ring_nf; finish

-- R4/R0 drain: each round consumes 1 from both a and c, adds 2 to e
theorem r4r0_chain : ∀ k, ∀ a e,
    ⟨a + k + 1, 0, a + k, 0, e⟩ [fm]⊢* ⟨a + 1, 0, a, 0, e + 2 * k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
      show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h a (e + 2))
  ring_nf; finish

-- Main transition: (1, 0, 0, 0, e) ⊢⁺ (1, 0, 0, 0, 2*e + 3)
theorem main_trans (e : ℕ) : ⟨1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2 * e + 3⟩ := by
  -- Phase 1: R4 then R1
  apply step_stepStar_stepPlus
  · show fm ⟨0 + 1, 0, 0, 0, e⟩ = some ⟨0, 0 + 1, 0, 0, e + 2⟩; simp [fm]
  -- Now at (0, 1, 0, 0, e+2)
  apply stepStar_trans (c₂ := ⟨1, 0, 0, 3, e + 2⟩)
  · step fm; finish
  -- Phase 2: R2/R1 chain with e+2 rounds
  -- We have (1, 0, 0, 3, e+2) = (1, 0, 0, 2+1, 0+(e+2))
  apply stepStar_trans (c₂ := ⟨e + 3, 0, 0, 2 * e + 7, 0⟩)
  · have h2 := r2r1_chain (e + 2) 1 2 0
    simp only [Nat.zero_add] at h2
    rw [show (2 : ℕ) + 1 = 3 from by ring,
        show 1 + (e + 2) = e + 3 from by ring,
        show 2 + 1 + 2 * (e + 2) = 2 * e + 7 from by ring] at h2
    exact h2
  -- Phase 3: R3 chain, (e+3) rounds
  -- (e+3, 0, 0, 2*e+7, 0) = (e+3, 0, 0, 1 + 2*(e+3), 0)
  apply stepStar_trans (c₂ := ⟨e + 3, 0, e + 3, 1, 0⟩)
  · have h3 := r3_chain (e + 3) (e + 3) 0 1
    simp only [Nat.zero_add] at h3
    rw [show 1 + 2 * (e + 3) = 2 * e + 7 from by ring] at h3
    exact h3
  -- Phase 4: 4 opening steps then R4/R0 chain
  -- (e+3, 0, e+3, 1, 0) -R4-> (e+2, 1, e+3, 1, 2) -R0-> (e+2, 0, e+2, 1, 2)
  -- -R2-> (e+2, 1, e+2, 0, 1) -R0-> (e+2, 0, e+1, 0, 1)
  apply stepStar_trans (c₂ := ⟨e + 2, 0, e + 1, 0, 1⟩)
  · rw [show e + 3 = (e + 2) + 1 from by ring]
    step fm  -- R4
    rw [show (e + 2) + 1 = (e + 1) + 1 + 1 from by ring]
    step fm  -- R0
    rw [show (1 : ℕ) = 0 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    step fm  -- R2
    rw [show (e + 1) + 1 = e + 1 + 1 from by ring]
    step fm  -- R0
    finish
  -- Phase 5: R4/R0 chain, e+1 rounds
  -- (e+2, 0, e+1, 0, 1) = (0+(e+1)+1, 0, 0+(e+1), 0, 1)
  -- r4r0_chain (e+1) 0 1: →* (0+1, 0, 0, 0, 1+2*(e+1)) = (1, 0, 0, 0, 2*e+3)
  have h5 := r4r0_chain (e + 1) 0 1
  simp only [Nat.zero_add] at h5
  rw [show (e + 1) + 1 = e + 2 from by ring,
      show 1 + 2 * (e + 1) = 2 * e + 3 from by ring] at h5
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨1, 0, 0, 0, e⟩) 0
  intro e; exact ⟨2 * e + 3, main_trans e⟩
