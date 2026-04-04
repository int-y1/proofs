import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1823: [9/10, 55/21, 44/3, 7/11, 15/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  1
 0  0  0  1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1823

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R2-R1 chain: d rounds of R2 then R1, draining d while building b and e.
-- (X+D, Y+1, 0, D, E) →* (X, Y+1+D, 0, 0, E+D)
theorem r2r1_chain : ∀ D, ∀ X Y E, ⟨X + D, Y + 1, 0, D, E⟩ [fm]⊢* ⟨X, Y + 1 + D, 0, 0, E + D⟩ := by
  intro D; induction' D with D ih <;> intro X Y E
  · exists 0
  · rw [show X + (D + 1) = X + D + 1 from by ring]
    step fm
    step fm
    rw [show Y + 1 + 1 = (Y + 1) + 1 from by ring]
    apply stepStar_trans (ih X (Y + 1) (E + 1))
    ring_nf; finish

-- R3 chain: drain b, adding 2 to a and 1 to e per step.
-- (A, B, 0, 0, E) →* (A+2*B, 0, 0, 0, E+B)
theorem r3_chain : ∀ B, ∀ A E, ⟨A, B, 0, 0, E⟩ [fm]⊢* ⟨A + 2 * B, 0, 0, 0, E + B⟩ := by
  intro B; induction' B with B ih <;> intro A E
  · exists 0
  · step fm
    apply stepStar_trans (ih (A + 2) (E + 1))
    ring_nf; finish

-- R4 chain: move e to d.
-- (A, 0, 0, D, K) →* (A, 0, 0, D+K, 0)
theorem e_to_d : ∀ K, ∀ A D, ⟨A, 0, 0, D, K⟩ [fm]⊢* ⟨A, 0, 0, D + K, 0⟩ := by
  intro K; induction' K with K ih <;> intro A D
  · exists 0
  · rw [show D + (K + 1) = (D + 1) + K from by ring]
    step fm
    exact ih A (D + 1)

-- Main transition: (d+k+2, 0, 0, d, 0) →⁺ (2d+k+6, 0, 0, 2d+3, 0)
theorem main_trans : ⟨d + k + 2, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2 * d + k + 6, 0, 0, 2 * d + 3, 0⟩ := by
  rw [show d + k + 2 = (d + k + 1) + 1 from by ring]
  step fm
  step fm
  rw [show d + k = k + d from by ring]
  apply stepStar_trans (r2r1_chain d k 2 0)
  rw [show 2 + 1 + d = d + 3 from by ring, show 0 + d = d from by ring]
  apply stepStar_trans (r3_chain (d + 3) k d)
  rw [show k + 2 * (d + 3) = 2 * d + k + 6 from by ring,
      show d + (d + 3) = 2 * d + 3 from by ring]
  apply stepStar_trans (e_to_d (2 * d + 3) (2 * d + k + 6) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 3, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, d⟩ ↦ ⟨d + k + 2, 0, 0, d, 0⟩) ⟨0, 3⟩
  intro ⟨k, d⟩
  refine ⟨⟨k + 1, 2 * d + 3⟩, ?_⟩
  show ⟨d + k + 2, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2 * d + 3 + (k + 1) + 2, 0, 0, 2 * d + 3, 0⟩
  rw [show 2 * d + 3 + (k + 1) + 2 = 2 * d + k + 6 from by ring]
  exact main_trans
