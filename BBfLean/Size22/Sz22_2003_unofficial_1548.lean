import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1548: [7/30, 45/77, 11/3, 4/11, 21/2]

Vector representation:
```
-1 -1 -1  1  0
 0  2  1 -1 -1
 0 -1  0  0  1
 2  0  0  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1548

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3+R2 interleaved chain.
-- Each R3+R2 pair: (0, b+1, c, d+1, 0) → (0, b+2, c+1, d, 0).
-- k pairs: (0, b, c, d+k, 0) →* (0, b+k, c+k, d, 0), requires b ≥ 1.
theorem r3r2_chain : ∀ k b c d, ⟨0, b+1, c, d+k, 0⟩ [fm]⊢* ⟨0, b+k+1, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm  -- R3: (0, b, c, (d+k)+1, 1)
    step fm  -- R2: (0, b+2, c+1, d+k, 0)
    rw [show b + 2 = (b + 1) + 1 from by omega]
    apply stepStar_trans (ih (b + 1) (c + 1) d)
    ring_nf; finish

-- R3 drain b to e: (0, b+k, c, 0, e) →* (0, b, c, 0, e+k).
theorem b_to_e : ∀ k b c e, ⟨0, b+k, c, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by omega]
    step fm  -- R3: (0, b+k, c, 0, e+1)
    apply stepStar_trans (ih b c (e + 1))
    ring_nf; finish

-- R4 drain e to a: (a, 0, c, 0, e+k) →* (a+2*k, 0, c, 0, e).
theorem e_to_a : ∀ k a c e, ⟨a, 0, c, 0, e+k⟩ [fm]⊢* ⟨a+2*k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by omega]
    step fm  -- R4: (a+2, 0, c, 0, e+k)
    apply stepStar_trans (ih (a + 2) c e)
    ring_nf; finish

-- R5+R1 chain: each pair (a+2, 0, c+1, d, 0) →R5 (a+1, 1, c+1, d+1, 0) →R1 (a, 0, c, d+2, 0).
-- k pairs: (a+2*k, 0, c+k, d, 0) →* (a, 0, c, d+2*k, 0).
theorem r5r1_chain : ∀ k a c d, ⟨a+2*k, 0, c+k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + 2 * (k + 1) = a + 2 * k + 2 from by ring,
        show c + (k + 1) = c + k + 1 from by ring]
    -- Goal: (a+2*k+2, 0, c+k+1, d, 0) →* (a, 0, c, d+2*(k+1), 0)
    -- First R5: needs a+2*k+2 ≥ 1 (always true since ≥ 2)
    step fm  -- R5: (a+2*k+1, 1, c+k+1, d+1, 0)
    -- Then R1: needs a+2*k+1 ≥ 1 (yes), b=1 ≥ 1, c+k+1 ≥ 1 (yes)
    step fm  -- R1: (a+2*k, 0, c+k, d+2, 0)
    apply stepStar_trans (ih a c (d + 2))
    ring_nf; finish

-- Compose all phases: (0, 2, 1, D, 0) →* (2, 0, 0, 2*D+2, 0).
theorem all_phases (D : ℕ) : ⟨0, 2, 1, D, 0⟩ [fm]⊢* ⟨2, 0, 0, 2*D+2, 0⟩ := by
  -- R3+R2 chain: (0, 2, 1, D, 0) → (0, D+2, D+1, 0, 0)
  have h1 := r3r2_chain D 1 1 0
  rw [show (1 : ℕ) + 1 = 2 from by omega, show 0 + D = D from by omega] at h1
  apply stepStar_trans h1
  -- Now goal has (0, 1+D+1, 1+D, 0, 0). Normalize.
  rw [show 1 + D + 1 = 0 + (D + 2) from by omega]
  -- R3 drain: (0, 0+(D+2), 1+D, 0, 0) → (0, 0, 1+D, 0, 0+(D+2))
  apply stepStar_trans (b_to_e (D + 2) 0 (1 + D) 0)
  -- R4 drain: (0, 0, 1+D, 0, 0+(D+2)) → (0+2*(D+2), 0, 1+D, 0, 0)
  apply stepStar_trans (e_to_a (D + 2) 0 (1 + D) 0)
  -- R5+R1 chain: need to match (a+2*k, 0, c+k, d, 0)
  rw [show 0 + 2 * (D + 2) = 2 + 2 * (D + 1) from by ring,
      show 1 + D = 0 + (D + 1) from by omega]
  apply stepStar_trans (r5r1_chain (D + 1) 2 0 0)
  ring_nf; finish

-- Main transition: (2, 0, 0, D, 0) →⁺ (2, 0, 0, 2*D+2, 0).
theorem main_trans : ⟨2, 0, 0, D, 0⟩ [fm]⊢⁺ ⟨2, 0, 0, 2*D+2, 0⟩ := by
  -- 6 bootstrap steps: (2,0,0,D,0) → (0,2,1,D,0)
  step fm  -- R5: (1,1,0,D+1,0)
  step fm  -- R3: (1,0,0,D+1,1)
  step fm  -- R2: (1,2,1,D,0)
  step fm  -- R1: (0,1,0,D+1,0)
  step fm  -- R3: (0,0,0,D+1,1)
  step fm  -- R2: (0,2,1,D,0)
  exact all_phases D

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨2, 0, 0, d, 0⟩) 2
  intro d; exists 2 * d + 2; exact main_trans

end Sz22_2003_unofficial_1548
