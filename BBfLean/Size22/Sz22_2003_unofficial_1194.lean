import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1194: [5/6, 49/2, 484/35, 3/11, 6/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  2
 0  1  0  0 -1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1194

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 chain: move e to b
theorem e_to_b : ∀ j, ⟨0, b, 0, d, e + j⟩ [fm]⊢* ⟨0, b + j, 0, d, e⟩ := by
  intro j; induction' j with j ih generalizing b d e
  · exists 0
  · rw [Nat.add_succ e j]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R1R1R3 chain: j rounds
-- (2, 2*j, c, d+j, e) →* (2, 0, c+j, d, e+2*j)
theorem r1r1r3_chain : ∀ j c d e, ⟨2, 2 * j, c, d + j, e⟩ [fm]⊢* ⟨2, 0, c + j, d, e + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  · rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by ring]
    step fm
    rw [show d + (j + 1) = d + j + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c + 1) d (e + 2))
    ring_nf; finish

-- R3R2R2 drain: j rounds
-- (0, 0, c+j, d+j, e) →* (0, 0, c, d+4*j, e+2*j)
theorem r3r2r2_drain : ∀ j c d e, ⟨0, 0, c + j, d + j, e⟩ [fm]⊢* ⟨0, 0, c, d + 4 * j, e + 2 * j⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  · rw [show c + (j + 1) = c + j + 1 from by ring,
        show d + (j + 1) = d + j + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + j + 2 + 2 = (d + 4) + j from by ring]
    apply stepStar_trans (ih c (d + 4) (e + 2))
    ring_nf; finish

-- Inner transition: from R5 onwards
-- (0, b+1, 0, d+1, 0) →⁺ result via R5, R1, R3, R1R1R3 chain, R2R2, drain
-- But let's just build the transition for the specific form we need.

-- (2, 2*(k+1), 0, (k+1)+(k+1), 2) →* (0, 0, 0, 4*(k+2), 4*k+6)
theorem r1r1r3_to_end (k : ℕ) :
    ⟨2, 2 * (k + 1), 0, (k + 1) + (k + 1), 2⟩ [fm]⊢* ⟨0, 0, 0, 4 * (k + 2), 4 * k + 6⟩ := by
  apply stepStar_trans (r1r1r3_chain (k + 1) 0 (k + 1) 2)
  -- at (2, 0, k+1, k+1, 2+2*(k+1))
  step fm  -- R2
  step fm  -- R2
  -- at (0, 0, k+1, k+1+2+2, 2+2*(k+1))
  rw [show (0 : ℕ) + (k + 1) = 0 + (k + 1) from rfl,
      show (k + 1 + 2 + 2 : ℕ) = 4 + (k + 1) from by ring,
      show (0 : ℕ) + (k + 1) = 0 + (k + 1) from rfl]
  apply stepStar_trans (r3r2r2_drain (k + 1) 0 4 (2 + 2 * (k + 1)))
  ring_nf; finish

-- Main transition
theorem main_trans : ∀ k, ⟨0, 0, 0, 2 * (k + 1), 2 * k⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * (k + 1), 4 * k + 2⟩ := by
  intro k; rcases k with _ | k
  · execute fm 5
  · -- k+1 ≥ 1: (0,0,0,2k+4,2k+2) →⁺ (0,0,0,4k+8,4k+6)
    rw [show 2 * (k + 1) = 0 + (2 * k + 2) from by ring]
    apply stepStar_stepPlus_stepPlus (e_to_b (2 * k + 2) (b := 0) (d := 2 * (k + 1 + 1)) (e := 0))
    -- at (0, 2k+2, 0, 2*(k+2), 0). R5.
    rw [show (0 : ℕ) + (2 * k + 2) = (2 * k + 1) + 1 from by ring,
        show 2 * (k + 1 + 1) = (2 * k + 3) + 1 from by ring]
    step fm  -- R5
    step fm  -- R1
    rw [show (2 * k + 3 : ℕ) = (2 * k + 2) + 1 from by ring]
    step fm  -- R3
    -- at (2, (2k+1)+1, 0, 2k+2, 2)
    -- Need to massage into form for r1r1r3_to_end
    rw [show 4 * (k + 1 + 1) = 4 * (k + 2) from by ring,
        show 4 * (k + 1) + 2 = 4 * k + 6 from by ring]
    -- Goal: (2, (2k+1)+1, 0, 2k+2, 2) ⊢* (0, 0, 0, 4*(k+2), 4*k+6)
    -- (2k+1)+1 = 2*(k+1). 2k+2 = (k+1)+(k+1).
    rw [show (2 * k + 1 : ℕ) + 1 = 2 * (k + 1) from by ring]
    have h : (⟨2, 2 * (k + 1), 0, 2 * (k + 1), 2⟩ : Q) =
      ⟨2, 2 * (k + 1), 0, (k + 1) + (k + 1), 2⟩ := by ring_nf
    rw [h]
    exact r1r1r3_to_end k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 0, 2 * (k + 1), 2 * k⟩) 0
  intro k; exists 2 * k + 1
  rw [show 2 * (2 * k + 1 + 1) = 4 * (k + 1) from by ring,
      show 2 * (2 * k + 1) = 4 * k + 2 from by ring]
  exact main_trans k

end Sz22_2003_unofficial_1194
