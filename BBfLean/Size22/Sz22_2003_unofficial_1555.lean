import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1555: [7/30, 9/2, 44/21, 5/11, 49/3]

Vector representation:
```
-1 -1 -1  1  0
-1  2  0  0  0
 2 -1  0 -1  1
 0  0  1  0 -1
 0 -1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1555

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | _ => none

-- R4 repeated: move e to c.
theorem e_to_c : ∀ k, ⟨0, b, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R3/R1/R1 chain: k rounds draining c by 2 each, b by 3 each.
theorem r3r1r1_chain : ∀ k, ⟨0, b + 3 * k, 2 * k + c, d + 1, e⟩ [fm]⊢*
    ⟨0, b, c, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · ring_nf; finish
  · rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show 2 * (k + 1) + c = 2 * k + (c + 2) from by ring]
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih (b := b) (c := c) (d := d + 1) (e := e + 1))
    ring_nf; finish

-- R3/R2/R2 chain: k rounds, each increasing b by 3, draining d by 1, increasing e by 1.
theorem r3r2r2_chain : ∀ k, ⟨0, b + 1, 0, d + k, e⟩ [fm]⊢*
    ⟨0, b + 3 * k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    apply stepStar_trans (ih (b := b + 3) (d := d) (e := e + 1))
    ring_nf; finish

-- Phase A + B combined: e_to_c then R5 then r3r1r1_chain.
theorem phases_ab (n : ℕ) :
    ⟨0, 5 * n + 7, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨0, 2 * n + 3, 0, n + 3, n + 1⟩ := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm  -- R4: (0, 5n+7, 1, 0, 2n+1)
  rw [show 2 * n + 1 = 0 + (2 * n + 1) from by ring]
  apply stepStar_trans (e_to_c (2 * n + 1) (b := 5 * n + 7) (c := 1) (e := 0))
  -- Now at (0, 5n+7, 2n+2, 0, 0)
  rw [show 1 + (2 * n + 1) = 2 * n + 2 from by ring]
  step fm  -- R5: (0, 5n+6, 2n+2, 2, 0)
  rw [show 5 * n + 6 = (2 * n + 3) + 3 * (n + 1) from by ring,
      show 2 * n + 2 = 2 * (n + 1) + 0 from by ring,
      show (2 : ℕ) = 0 + 1 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain (n + 1) (b := 2 * n + 3) (c := 0) (d := 0 + 1) (e := 0))
  ring_nf; finish

-- Main transition: (0, 5n+7, 0, 0, 2n+2) ⊢⁺ (0, 5n+12, 0, 0, 2n+4)
theorem main_trans (n : ℕ) :
    ⟨0, 5 * n + 7, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨0, 5 * n + 12, 0, 0, 2 * n + 4⟩ := by
  apply stepPlus_stepStar_stepPlus (phases_ab n)
  -- Now at (0, 2n+3, 0, n+3, n+1)
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring,
      show n + 3 = 0 + (n + 3) from by ring]
  apply stepStar_trans (r3r2r2_chain (n + 3) (b := 2 * n + 2) (d := 0) (e := n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 7, 0, 0, 2⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 5 * n + 7, 0, 0, 2 * n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1555
