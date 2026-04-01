import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1430: [7/15, 22/3, 297/14, 5/11, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
-1  3  0 -1  1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1430

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer e to c.
theorem e_to_c : ∀ k a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e; rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

-- R3+R2 chain: drain d with c=0. Each round: R3 then R2 x3.
theorem r3_r2_chain : ∀ k a d e, ⟨a + 1, 0, 0, d + 1 + k, e⟩ [fm]⊢* ⟨a + 2 * k + 3, 0, 0, d, e + 4 * k + 4⟩ := by
  intro k; induction' k with k ih
  · intro a d e; step fm; step fm; step fm; step fm; ring_nf; finish
  · intro a d e
    rw [show d + 1 + (k + 1) = (d + 1 + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) d (e + 4))
    ring_nf; finish

-- R3+R1 chain: drain c in chunks of 3.
theorem r3_r1_chain : ∀ k a c d e, ⟨a + k, 0, c + 3 * k, d + 1, e⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a c d e; exists 0
  · intro a c d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring]
    step fm; step fm; step fm; step fm
    rw [show d + 1 + 2 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih a c (d + 2) (e + 1))
    ring_nf; finish

-- Main transition: (m+q+2, 0, 3q+2, 0, 0) ⊢⁺ (m+4q+6, 0, 9q+11, 0, 0).
-- Phases: R5+R1 opening, q rounds R3+3R1, remainder R3+R1+R2x2, R3+R2 chain, R4 chain.
theorem main_trans (m q : ℕ) :
    ⟨m + q + 2, 0, 3 * q + 2, 0, 0⟩ [fm]⊢⁺ ⟨m + 4 * q + 6, 0, 9 * q + 11, 0, 0⟩ := by
  -- Opening: R5+R1. (m+q+2, 0, 3q+2, 0, 0) -> (m+q+1, 0, 3q+1, 2, 0)
  step fm; step fm
  rw [show m + q + 1 = (m + 1) + q from by ring,
      show 3 * q + 1 = 1 + 3 * q from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3_r1_chain q (m + 1) 1 1 0)
  -- Now at (m+1, 0, 1, 1+2q+1, 0+q) = (m+1, 0, 1, 2q+2, q).
  -- Remainder: R3 + R1 + R2 x2.
  rw [show 1 + 2 * q + 1 = (2 * q + 1) + 1 from by ring,
      show (0 : ℕ) + q = q from by ring]
  step fm; step fm; step fm; step fm
  -- R3: (m, 3, 1, 2q+1, q+1). R1: (m, 2, 0, 2q+2, q+1).
  -- R2: (m+1, 1, 0, 2q+2, q+2). R2: (m+2, 0, 0, 2q+2, q+3).
  rw [show 2 * q + 2 = 0 + 1 + (2 * q + 1) from by ring]
  apply stepStar_trans (r3_r2_chain (2 * q + 1) (m + 1) 0 (q + 3))
  -- Now at (m+2*(2q+1)+1+3, 0, 0, 0, q+3+4*(2q+1)+4) = (m+4q+6, 0, 0, 0, 9q+11).
  rw [show q + 3 + 4 * (2 * q + 1) + 4 = 0 + (9 * q + 11) from by ring]
  apply stepStar_trans (e_to_c (9 * q + 11) (m + 1 + 2 * (2 * q + 1) + 3) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 5, 0, 0⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, q⟩ ↦ ⟨m + q + 2, 0, 3 * q + 2, 0, 0⟩) ⟨0, 1⟩
  intro ⟨m, q⟩
  refine ⟨⟨m + q + 1, 3 * q + 3⟩, ?_⟩
  show ⟨m + q + 2, 0, 3 * q + 2, 0, 0⟩ [fm]⊢⁺ ⟨m + q + 1 + (3 * q + 3) + 2, 0, 3 * (3 * q + 3) + 2, 0, 0⟩
  rw [show m + q + 1 + (3 * q + 3) + 2 = m + 4 * q + 6 from by ring,
      show 3 * (3 * q + 3) + 2 = 9 * q + 11 from by ring]
  exact main_trans m q

end Sz22_2003_unofficial_1430
