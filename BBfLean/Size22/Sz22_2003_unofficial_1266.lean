import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1266: [5/6, 99/35, 4/5, 7/11, 165/2]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1 -1  1
 2  0 -1  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1266

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

-- R2,R1,R1 chain: d-1 rounds drain D while building C and E.
theorem r2r1r1_chain : ∀ k a c D e,
    ⟨a + 2 * k, (0 : ℕ), c + 1, D + k, e⟩ [fm]⊢*
    ⟨a, (0 : ℕ), c + k + 1, D, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a c D e; simp; exists 0
  · intro a c D e
    rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show D + (k + 1) = (D + 1) + k from by ring]
    apply stepStar_trans (ih (a + 2) c (D + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    ring_nf; finish

-- R3 chain: drain c, adding 2 per unit to a.
theorem r3_chain : ∀ k a e,
    ⟨a, (0 : ℕ), k, (0 : ℕ), e⟩ [fm]⊢*
    ⟨a + 2 * k, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih
  · intro a e; simp; exists 0
  · intro a e
    step fm
    apply stepStar_trans (ih (a + 2) e)
    ring_nf; finish

-- R4 chain: drain e into d.
theorem r4_chain : ∀ k a D,
    ⟨a, (0 : ℕ), (0 : ℕ), D, k⟩ [fm]⊢*
    ⟨a, (0 : ℕ), (0 : ℕ), D + k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih
  · intro a D; simp; exists 0
  · intro a D
    step fm
    apply stepStar_trans (ih a (D + 1))
    ring_nf; finish

-- Main transition: (2*d+3, 0, 0, d+1, 0) →⁺ (2*d+5, 0, 0, d+2, 0) for all d.
theorem main_transition (d : ℕ) :
    ⟨2 * d + 3, (0 : ℕ), (0 : ℕ), d + 1, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨2 * d + 5, (0 : ℕ), (0 : ℕ), d + 2, (0 : ℕ)⟩ := by
  -- Phase 1: R5 + R1 opening
  step fm  -- R5: (2*d+2, 1, 1, d+1, 1)
  step fm  -- R1: (2*d+1, 0, 2, d+1, 1)
  -- Phase 2: R2,R1,R1 chain (d rounds)
  rw [show 2 * d + 1 = 1 + 2 * d from by ring,
      show (d + 1 : ℕ) = 1 + d from by ring]
  apply stepStar_trans (r2r1r1_chain d 1 1 1 1)
  rw [show 1 + d + 1 = d + 2 from by ring,
      show (1 + d : ℕ) = d + 1 from by ring]
  -- State: (1, 0, d+2, 1, d+1)
  -- Phase 3: R2 + R1
  step fm  -- R2: (1, 2, d+1, 0, d+2)
  step fm  -- R1: (0, 1, d+2, 0, d+2)
  -- Phase 4: R3 + R1
  step fm  -- R3: (2, 1, d+1, 0, d+2)
  step fm  -- R1: (1, 0, d+2, 0, d+2)
  -- Phase 5: R3 chain (d+2 rounds)
  apply stepStar_trans (r3_chain (d + 2) 1 (d + 2))
  rw [show 1 + 2 * (d + 2) = 2 * d + 5 from by ring]
  -- State: (2*d+5, 0, 0, 0, d+2)
  -- Phase 6: R4 chain (d+2 rounds)
  apply stepStar_trans (r4_chain (d + 2) (2 * d + 5) 0)
  rw [show 0 + (d + 2) = d + 2 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, n + 1, 0⟩) 0
  intro n
  exists n + 1
  exact main_transition n

end Sz22_2003_unofficial_1266
