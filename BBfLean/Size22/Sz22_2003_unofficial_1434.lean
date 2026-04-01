import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1434: [7/15, 22/3, 99/14, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
-1  2  0 -1  1
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1434

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3 chain: convert e to c in pairs.
theorem r3_chain : ∀ k a c, ⟨a, 0, c, 0, 2 * k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih
  · intro a c; exists 0
  · intro a c
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1)); ring_nf; finish

-- R2+R0+R0 chain: drain a and c together.
theorem r2_r0_r0_chain : ∀ k d e, ⟨k + 1, 0, 2 * k + 1, d + 1, e⟩ [fm]⊢* ⟨1, 0, 1, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d + 1) (e + 1)); ring_nf; finish

-- R2+R1+R1 chain: drain d, build a and e.
theorem r2_r1_r1_chain : ∀ k a d e, ⟨a + 1, 0, 0, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 3)); ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, 4n+4) ⊢⁺ (n+3, 0, 0, 0, 4n+8).
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, 4 * n + 4⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 4 * n + 8⟩ := by
  -- Phase 1: R3 chain, e→c. k = 2n+2.
  rw [show 4 * n + 4 = 2 * (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * n + 2) (n + 2) 0)
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring]
  -- Phase 2: R4 + R0. State: (n+2, 0, 2n+2, 0, 0).
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm; step fm
  -- State: (n+1, 0, 2n+1, 2, 0) = (n+1, 0, 2*n+1, 1+1, 0).
  -- Phase 3: R2+R0+R0 chain with k=n.
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r2_r0_r0_chain n 1 0)
  -- State: (1, 0, 1, 1+n+1, 0+n) = (1, 0, 1, n+2, n).
  rw [show 1 + n + 1 = (n + 1) + 1 from by ring,
      show (0 : ℕ) + n = n from by ring]
  -- Phase 4: R2 + R0 + R1.
  step fm; step fm; step fm
  -- State: (1, 0, 0, n+2, n+2).
  rw [show n + 1 + 1 = 0 + (n + 2) from by ring]
  -- Phase 5: R2+R1+R1 chain with k = n+2.
  apply stepStar_trans (r2_r1_r1_chain (n + 2) 0 0 (0 + (n + 2)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 4⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 4 * n + 4⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1434
