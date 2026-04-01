import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1234: [5/6, 7/2, 44/35, 3/11, 110/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  0
 2  0 -1 -1  1
 0  1  0  0 -1
 1  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1234

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: drain e to b. Requires a=0, c=0.
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R3,R1,R1 chain: each round transfers one unit from d to c, draining b by 2.
theorem r3r1r1_chain : ∀ k, ⟨0, 2 * k + 1, c + 1, k + 1, e⟩ [fm]⊢*
    ⟨0, 1, c + k + 1, 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show (k + 1) + 1 = (k + 1) + 1 from rfl]
    step fm  -- R3: (2, 2k+3, c, k+1, e+1)
    step fm  -- R1: (1, 2k+2, c+1, k+1, e+1)
    step fm  -- R1: (0, 2k+1, c+2, k+1, e+1)
    apply stepStar_trans (ih (c := c + 1) (e := e + 1))
    ring_nf; finish

-- R3,R2,R2 chain: each round transfers one unit from c to d, with e growing.
theorem r3r2r2_chain : ∀ k, ⟨0, 0, k, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · step fm  -- R3: (2, 0, k, d, e+1)
    step fm  -- R2: (1, 0, k, d+1, e+1)
    step fm  -- R2: (0, 0, k, d+2, e+1)
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, n+2, 2n+2) ⊢⁺ (0, 0, 0, n+3, 2n+4)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n + 2, 2 * n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 3, 2 * n + 4⟩ := by
  -- Phase 1: drain e to b: (0,0,0,n+2,2n+2) →* (0,2n+2,0,n+2,0)
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * n + 2) (b := 0) (d := n + 2) (e := 0))
  -- Now at (0, 2n+2, 0, n+2, 0)
  rw [show (0 + (2 * n + 2) : ℕ) = 2 * n + 2 from by ring,
      show n + 2 = (n + 1) + 1 from by ring]
  -- Phase 2: R5
  step fm
  -- Phase 3: R1
  step fm
  -- Phase 4: R3,R1,R1 chain (n rounds)
  apply stepStar_trans (r3r1r1_chain n (c := 1) (e := 1))
  rw [show 1 + n + 1 = n + 2 from by ring,
      show 1 + n = n + 1 from by ring]
  -- Phase 5: R3
  step fm
  -- Phase 6: R1
  step fm
  -- Phase 7: R2
  step fm
  -- Phase 8: R3,R2,R2 chain (n+2 rounds)
  apply stepStar_trans (r3r2r2_chain (n + 2) (d := 0) (e := n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 2 * n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1234
