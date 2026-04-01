import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1489: [7/15, 66/7, 1/3, 125/2, 1/55, 3/5]

Vector representation:
```
 0 -1 -1  1  0
 1  1  0 -1  1
 0 -1  0  0  0
-1  0  3  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1489

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1 (R4 chain): drain a, add 3 to c per step
theorem a_to_c : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e; step fm
    apply stepStar_trans (ih (c + 3) e); ring_nf; finish

-- Phase 2 (R5 chain): drain e, subtract from c
theorem c_e_drain : ∀ k c, ⟨0, 0, c + k, 0, k⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih
  · intro c; exists 0
  · intro c
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c); ring_nf; finish

-- Phase 4 (R1R2 chain): interleaved, consuming c, growing a and e
theorem r1r2_chain : ∀ k a e, ⟨a, 1, k, 0, e⟩ [fm]⊢* ⟨a + k, 1, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e; step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, n+2) ⊢⁺ (2n+3, 0, 0, 0, 2n+3)
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨2 * n + 3, 0, 0, 0, 2 * n + 3⟩ := by
  -- Phase 1 (first step): R4
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- Remaining R4 chain
  apply stepStar_trans (a_to_c (n + 1) 3 (n + 2))
  rw [show 3 + 3 * (n + 1) = 3 * n + 6 from by ring]
  -- Phase 2: R5 chain
  rw [show 3 * n + 6 = (2 * n + 4) + (n + 2) from by ring]
  apply stepStar_trans (c_e_drain (n + 2) (2 * n + 4))
  -- Phase 3: R6
  rw [show 2 * n + 4 = (2 * n + 3) + 1 from by ring]
  step fm
  -- Phase 4: R1R2 chain
  apply stepStar_trans (r1r2_chain (2 * n + 3) 0 0)
  ring_nf
  -- Phase 5: R3
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, n + 2⟩) 0
  intro n; exact ⟨2 * n + 1, main_trans n⟩

end Sz22_2003_unofficial_1489
