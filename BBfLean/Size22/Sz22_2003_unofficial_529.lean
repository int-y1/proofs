import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #529: [28/15, 39/22, 35/2, 11/13, 26/7]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  1
-1  0  1  1  0  0
 0  0  0  0  1 -1
 1  0  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_529

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | _ => none

-- R4 repeated: transfer f to e (when a=0, b=0)
theorem f_to_e : ⟨0, 0, c, d, e, k⟩ [fm]⊢* ⟨0, 0, c, d, e+k, 0⟩ := by
  have many_step : ∀ k e, ⟨0, 0, c, d, e, k⟩ [fm]⊢* ⟨0, 0, c, d, e+k, 0⟩ := by
    intro k; induction' k with k h <;> intro e
    · exists 0
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k e

-- R2,R1 chain: (g+1, 0, c+k, d, k, g+1) ⊢* (g+k+1, 0, c, d+k, 0, g+k+1)
-- Need g universally quantified for the induction to work
theorem r2r1_chain : ∀ k, ∀ g c d, ⟨g+1, 0, c+k, d, k, g+1⟩ [fm]⊢* ⟨g+k+1, 0, c, d+k, 0, g+k+1⟩ := by
  intro k; induction' k with k h <;> intro g c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show (k + 1) = k + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: transfer a to c,d (when b=0, e=0)
theorem r3_chain : ∀ k, ∀ c d, ⟨k, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, c+k, d+k, 0, f⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Main transition: (0, 0, n+1, d+1, 0, n) ⊢⁺ (0, 0, n+2, d+2*n+1, 0, n+1)
theorem main_trans :
    ⟨0, 0, n+1, d+1, 0, n⟩ [fm]⊢⁺ ⟨0, 0, n+2, d+2*n+1, 0, n+1⟩ := by
  -- Phase 1: f_to_e: (0, 0, n+1, d+1, 0, n) -> (0, 0, n+1, d+1, n, 0)
  apply stepStar_stepPlus_stepPlus (@f_to_e (n+1) (d+1) 0 n)
  rw [show (0 : ℕ) + n = n from by ring]
  -- Phase 2a: R5: (0, 0, n+1, d+1, n, 0) -> (1, 0, n+1, d, n, 1)
  step fm
  -- Now at (1, 0, n+1, d, n, 1)
  -- Phase 2b: r2r1_chain with g=0
  rw [show n + 1 = 1 + n from by ring]
  apply stepStar_trans (r2r1_chain n 0 1 d)
  rw [show 0 + n + 1 = n + 1 from by ring]
  -- Now at (n+1, 0, 1, d+n, 0, n+1)
  -- Phase 3: r3_chain
  apply stepStar_trans (r3_chain (f := n+1) (n+1) 1 (d+n))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 1, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, d⟩ ↦ ⟨0, 0, n+1, d+1, 0, n⟩) ⟨0, 0⟩
  intro ⟨n, d⟩
  exact ⟨⟨n+1, d+2*n⟩, main_trans⟩
