import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1559: [7/45, 121/5, 20/77, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
 0  0 -1  0  2
 2  0  1 -1 -1
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1559

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R3,R2 chain (b=0): (a, 0, 0, k, e+1) ⊢* (a+2k, 0, 0, 0, e+k+1)
theorem r3r2_b0 : ∀ k, ∀ a e, ⟨a, 0, 0, k, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; step fm
    show ⟨a + 2, 0, 0, k, e + 1 + 1⟩ [fm]⊢* ⟨a + 2 * (k + 1), 0, 0, 0, e + (k + 1) + 1⟩
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

-- R3,R2 chain (b=1): (a, 1, 0, k, e+1) ⊢* (a+2k, 1, 0, 0, e+k+1)
theorem r3r2_b1 : ∀ k, ∀ a e, ⟨a, 1, 0, k, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 1, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; step fm
    show ⟨a + 2, 1, 0, k, e + 1 + 1⟩ [fm]⊢* ⟨a + 2 * (k + 1), 1, 0, 0, e + (k + 1) + 1⟩
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

-- R4 chain: move e to b.
theorem r4_chain : ∀ k, ∀ a b, ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · step fm
    apply stepStar_trans (ih a (b + 1))
    ring_nf; finish

-- R5,R1 chain: (a+k, b+2k, 0, d, 0) ⊢* (a, b, 0, d+2k, 0)
theorem r5r1_chain : ∀ k, ∀ a b d, ⟨a + k, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by omega]
    step fm; step fm
    show ⟨a + k, b + 2 * k, 0, d + 1 + 1, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * (k + 1), 0⟩
    rw [show d + 1 + 1 = (d + 2) from by omega,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by omega]
    exact ih a b (d + 2)

-- Main transition: (a+3, 0, 0, 2*d+6, 0) ⊢⁺ (a+6*d+23, 0, 0, 2*d+12, 0)
-- Phases: R5, R2, R3R2×(2d+7), R4×(2d+9), R5R1×(d+4),
--         R5, R2, R3R2×(2d+9), R4×(2d+11), R5R1×(d+6)
theorem main_trans : ⟨a + 3, 0, 0, 2 * d + 6, 0⟩ [fm]⊢⁺ ⟨a + 6 * d + 23, 0, 0, 2 * d + 12, 0⟩ := by
  -- Phase 1: R5
  step fm
  rw [show 2 * d + 5 + 1 + 1 = 2 * d + 7 from by omega]
  -- (a+2, 0, 1, 2*d+7, 0)
  -- Phase 2: R2
  step fm
  -- (a+2, 0, 0, 2*d+7, 2). Since 2 = 1+1, apply r3r2_b0 with e=1.
  -- Phase 3: R3R2 chain × (2*d+7)
  apply stepStar_trans (r3r2_b0 (2 * d + 7) (a + 2) 1)
  -- (a+4*d+16, 0, 0, 0, 2*d+9)
  rw [show a + 2 + 2 * (2 * d + 7) = a + 4 * d + 16 from by ring,
      show 1 + (2 * d + 7) + 1 = 2 * d + 9 from by ring]
  -- Phase 4: R4 chain × (2*d+9)
  apply stepStar_trans (r4_chain (2 * d + 9) (a + 4 * d + 16) 0)
  -- (a+4*d+16, 2*d+9, 0, 0, 0)
  rw [show a + 4 * d + 16 = (a + 3 * d + 12) + (d + 4) from by ring,
      show 0 + (2 * d + 9) = 1 + 2 * (d + 4) from by ring]
  -- Phase 5: R5R1 chain × (d+4)
  apply stepStar_trans (r5r1_chain (d + 4) (a + 3 * d + 12) 1 0)
  -- (a+3*d+12, 1, 0, 2*d+8, 0)
  rw [show 0 + 2 * (d + 4) = 2 * d + 8 from by ring]
  -- Phase 6: R5
  apply stepStar_trans
    (step_stepStar (show ⟨a + 3 * d + 12, 1, 0, 2 * d + 8, 0⟩ [fm]⊢
      ⟨a + 3 * d + 11, 1, 1, 2 * d + 9, 0⟩ from by
      rw [show a + 3 * d + 12 = (a + 3 * d + 11) + 1 from by ring]; simp [fm]))
  -- Phase 7: R2 (b=1 < 2, so R1 won't fire; R2 fires)
  apply stepStar_trans
    (step_stepStar (show ⟨a + 3 * d + 11, 1, 1, 2 * d + 9, 0⟩ [fm]⊢
      ⟨a + 3 * d + 11, 1, 0, 2 * d + 9, 2⟩ from by simp [fm]))
  -- (a+3*d+11, 1, 0, 2*d+9, 2). Since 2 = 1+1, apply r3r2_b1 with e=1.
  -- Phase 8: R3R2 chain with b=1 × (2*d+9)
  apply stepStar_trans (r3r2_b1 (2 * d + 9) (a + 3 * d + 11) 1)
  -- (a+7*d+29, 1, 0, 0, 2*d+11)
  rw [show a + 3 * d + 11 + 2 * (2 * d + 9) = a + 7 * d + 29 from by ring,
      show 1 + (2 * d + 9) + 1 = 2 * d + 11 from by ring]
  -- Phase 9: R4 chain × (2*d+11)
  apply stepStar_trans (r4_chain (2 * d + 11) (a + 7 * d + 29) 1)
  -- (a+7*d+29, 2*d+12, 0, 0, 0)
  rw [show a + 7 * d + 29 = (a + 6 * d + 23) + (d + 6) from by ring,
      show 1 + (2 * d + 11) = 0 + 2 * (d + 6) from by ring]
  -- Phase 10: R5R1 chain × (d+6)
  apply stepStar_trans (r5r1_chain (d + 6) (a + 6 * d + 23) 0 0)
  rw [show 0 + 2 * (d + 6) = 2 * d + 12 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 6, 0⟩) (by execute fm 28)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 3, 0, 0, 2 * d + 6, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩; exact ⟨⟨a + 6 * d + 20, d + 3⟩, main_trans⟩

end Sz22_2003_unofficial_1559
