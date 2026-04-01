import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1287: [63/10, 1/231, 14/3, 11/2, 75/11]

Vector representation:
```
-1  2 -1  1  0
 0 -1  0 -1 -1
 1 -1  0  1  0
-1  0  0  0  1
 0  1  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1287

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

-- R4 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d, e+k)
theorem r4_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (e := e + 1))
    ring_nf; finish

-- R5-R2 chain: k pairs from (0, 0, c, d+k, e+2*k) →* (0, 0, c+2*k, d, e)
theorem r5r2_chain : ∀ k, ⟨0, 0, c, d + k, e + 2 * k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

-- Final drain: (0, 0, c, d+1, 3) →* (1, 0, c+4, d+1, 0)
theorem final_drain : ⟨0, 0, c, d + 1, 3⟩ [fm]⊢* ⟨1, 0, c + 4, d + 1, 0⟩ := by
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm  -- R5: (0, 1, c+2, d+1, 2)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm  -- R2: (0, 0, c+2, d, 1)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm  -- R5: (0, 1, c+4, d, 0)
  step fm  -- R3: (1, 0, c+4, d+1, 0)
  finish

-- R1-R3 interleave: (1, j, k+1, D, 0) →* (0, j+k+2, 0, D+2*k+1, 0)
theorem r1r3_interleave : ∀ k, ⟨1, j, k + 1, D, 0⟩ [fm]⊢* ⟨0, j + k + 2, 0, D + 2 * k + 1, 0⟩ := by
  intro k; induction' k with k ih generalizing j D
  · step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm
    step fm
    rw [show D + 1 + 1 = D + 2 from by ring]
    apply stepStar_trans (ih (j := j + 1) (D := D + 2))
    ring_nf; finish

-- R3 chain: (a, b+k, 0, d, 0) →* (a+k, b, 0, d+k, 0)
theorem r3_chain : ∀ k, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (d := d + 1))
    ring_nf; finish

-- Main transition: (2*n+3, 0, 0, d+n+1, 0) ⊢⁺ (2*n+5, 0, 0, d+6*n+13, 0)
theorem main_trans : ⟨2 * n + 3, 0, 0, d + n + 1, 0⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, d + 6 * n + 13, 0⟩ := by
  -- Phase 1: R4 chain
  rw [show 2 * n + 3 = 0 + (2 * n + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * n + 3) (a := 0) (d := d + n + 1) (e := 0))
  -- Now at (0, 0, 0, d+n+1, 2*n+3)
  -- Phase 2: R5-R2 chain (n pairs)
  rw [show d + n + 1 = (d + 1) + n from by ring,
      show 0 + (2 * n + 3) = 3 + 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus (r5r2_chain n (c := 0) (d := d + 1) (e := 3))
  -- Now at (0, 0, 2*n, d+1, 3)
  -- Phase 3: Final drain
  rw [show 0 + 2 * n = 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus (final_drain (c := 2 * n) (d := d))
  -- Now at (1, 0, 2*n+4, d+1, 0)
  -- Phase 4: R1-R3 interleave
  rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r1r3_interleave (2 * n + 3) (j := 0) (D := d + 1))
  -- Now at (0, 2*n+5, 0, d+1+2*(2*n+3)+1, 0) = (0, 2*n+5, 0, d+4*n+8, 0)
  -- Phase 5: R3 chain (2*n+5 steps)
  rw [show 0 + (2 * n + 3) + 2 = (2 * n + 4) + 1 from by ring,
      show d + 1 + 2 * (2 * n + 3) + 1 = d + 4 * n + 8 from by ring]
  step fm  -- R3: (1, 2*n+4, 0, d+4*n+9, 0)
  rw [show 2 * n + 4 = 0 + (2 * n + 4) from by ring,
      show d + 4 * n + 7 + 1 + 1 = d + 4 * n + 9 from by ring]
  apply stepStar_trans (r3_chain (2 * n + 4) (a := 1) (b := 0) (d := d + 4 * n + 9))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 7, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨2 * p.1 + 3, 0, 0, p.2 + p.1 + 1, 0⟩) ⟨0, 6⟩
  intro ⟨n, d⟩
  refine ⟨⟨n + 1, d + 5 * n + 11⟩, ?_⟩
  show ⟨2 * n + 3, 0, 0, d + n + 1, 0⟩ [fm]⊢⁺ ⟨2 * (n + 1) + 3, 0, 0, (d + 5 * n + 11) + (n + 1) + 1, 0⟩
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
      show (d + 5 * n + 11) + (n + 1) + 1 = d + 6 * n + 13 from by ring]
  exact main_trans

end Sz22_2003_unofficial_1287
