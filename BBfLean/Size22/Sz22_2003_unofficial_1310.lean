import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1310: [63/10, 121/2, 4/77, 5/3, 6/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 2  0  0 -1 -1
 0 -1  1  0  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1310

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R3/R2/R2 chain: each round (R3, R2, R2) reduces d by 1 and increases e by 3.
-- (0, b, 0, d+k, e+k) →* (0, b, 0, d, e+4k)
theorem r3r2r2_chain : ∀ k b d e, ⟨(0 : ℕ), b, (0 : ℕ), d + k, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b, (0 : ℕ), d, e + 4 * k⟩ := by
  intro k; induction' k with k ih
  · intro b d e; simp; exists 0
  · intro b d e
    rw [show d + (k + 1) = (d + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih b (d + 1) (e + 1))
    rw [show e + 1 + 4 * k = e + 4 * k + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show e + 4 * k + 4 = e + 4 * (k + 1) from by ring]
    finish

-- R3/R1/R1 chain: each round (R3, R1, R1) reduces c by 2, increases b by 4, d by 1, e by -1.
-- (0, b, 2k, d+1, e+k) →* (0, b+4k, 0, d+k+1, e)
theorem r3r1r1_chain : ∀ k b d e, ⟨(0 : ℕ), b, 2 * k, d + 1, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + 4 * k, 0, d + k + 1, e⟩ := by
  intro k; induction' k with k ih
  · intro b d e; simp; exists 0
  · intro b d e
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 4) (d + 1) e)
    rw [show b + 4 + 4 * k = b + 4 * (k + 1) from by ring,
        show d + 1 + k + 1 = d + (k + 1) + 1 from by ring]
    finish

-- R4 chain: move b to c when a=0, d=0.
-- (0, b+k, c, 0, e) →* (0, b, c+k, 0, e)
theorem b_to_c : ∀ k b c e, ⟨(0 : ℕ), b + k, c, (0 : ℕ), e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih
  · intro b c e; exists 0
  · intro b c e
    rw [show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih (b + 1) c e)
    step fm
    rw [show c + k + 1 = c + (k + 1) from by ring]
    finish

-- Main transition: (0, 0, 2k+1, 0, 2k+3) →⁺ (0, 0, 4k+3, 0, 4k+5)
theorem main_trans (k : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 2 * k + 1, (0 : ℕ), 2 * k + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 4 * k + 3, (0 : ℕ), 4 * k + 5⟩ := by
  -- Phase 0: R5+R1 opening
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring,
      show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
  step fm
  step fm
  -- State: (0, 3, 2k, 1, 2k+2)
  -- Phase 1: R3/R1/R1 chain with k rounds
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 2 * k + 2 = (k + 2) + k from by ring]
  apply stepStar_trans (r3r1r1_chain k 3 0 (k + 2))
  rw [show 3 + 4 * k = 4 * k + 3 from by ring,
      show 0 + k + 1 = k + 1 from by ring]
  -- State: (0, 4k+3, 0, k+1, k+2)
  -- Phase 2: R3/R2/R2 chain with k+1 rounds
  rw [show k + 1 = 0 + (k + 1) from by ring,
      show k + 2 = 1 + (k + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) (4 * k + 3) 0 1)
  rw [show 1 + 4 * (k + 1) = 4 * k + 5 from by ring]
  -- State: (0, 4k+3, 0, 0, 4k+5)
  -- Phase 3: R4 chain
  rw [show 4 * k + 3 = 0 + (4 * k + 3) from by ring]
  apply stepStar_trans (b_to_c (4 * k + 3) 0 0 (4 * k + 5))
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 3⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 2 * k + 1, 0, 2 * k + 3⟩) 0
  intro k
  exists k + k + 1
  rw [show 2 * (k + k + 1) + 1 = 4 * k + 3 from by ring,
      show 2 * (k + k + 1) + 3 = 4 * k + 5 from by ring]
  exact main_trans k

end Sz22_2003_unofficial_1310
