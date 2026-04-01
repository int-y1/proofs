import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1561: [7/45, 20/3, 3/14, 11/2, 63/11]

Vector representation:
```
 0 -2 -1  1  0
 2 -1  1  0  0
-1  1  0 -1  0
-1  0  0  0  1
 0  2  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1561

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- Phase 1: R5/R1 chain.
theorem r5r1_chain : ∀ k, ∀ c d e, ⟨0, 0, c + k, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih c (d + 2) e); ring_nf; finish

-- Phase 2: R3/R2 chain. One round: R3 then R2.
theorem r3r2_chain : ∀ k, ∀ a c e, ⟨a + 1, 0, c, k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (c + 1) e); ring_nf; finish

-- Phase 3: R4 drain.
theorem r4_drain : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih c (e + 1)); ring_nf; finish

-- Main transition: (0, 0, c+3, 0, c+n+5) ⊢⁺ (0, 0, 2c+9, 0, 2c+n+12)
theorem main_trans (c n : ℕ) :
    ⟨0, 0, c + 3, 0, c + n + 5⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 9, 0, 2 * c + n + 12⟩ := by
  -- Phase 1: R5/R1 chain for c+3 rounds
  rw [show c + 3 = 0 + (c + 3) from by ring,
      show c + n + 5 = (n + 2) + (c + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (c + 3) 0 0 (n + 2))
  rw [show (0 + 2 * (c + 3) : ℕ) = 2 * c + 6 from by ring]
  -- Phase 1.5: R5, R2, R2
  rw [show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
  step fm; step fm; step fm
  -- Phase 2: R3/R2 chain for 2c+7 rounds
  -- State: (4, 0, 2, 2c+7, n+1) = (3+1, 0, 2, 2c+7, n+1)
  apply stepStar_trans (r3r2_chain (2 * c + 7) 3 2 (n + 1))
  rw [show 3 + (2 * c + 7) + 1 = 2 * c + 11 from by ring,
      show 2 + (2 * c + 7) = 2 * c + 9 from by ring]
  -- Phase 3: R4 drain
  apply stepStar_trans (r4_drain (2 * c + 11) (2 * c + 9) (n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 5⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, n⟩ ↦ ⟨0, 0, c + 3, 0, c + n + 5⟩) ⟨0, 0⟩
  intro ⟨c, n⟩
  refine ⟨⟨2 * c + 6, n + 1⟩, ?_⟩
  show ⟨0, 0, c + 3, 0, c + n + 5⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 6 + 3, 0, 2 * c + 6 + (n + 1) + 5⟩
  rw [show 2 * c + 6 + 3 = 2 * c + 9 from by ring,
      show 2 * c + 6 + (n + 1) + 5 = 2 * c + n + 12 from by ring]
  exact main_trans c n

end Sz22_2003_unofficial_1561
