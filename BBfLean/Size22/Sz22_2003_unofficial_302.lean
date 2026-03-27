import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #302: [15/2, 4/21, 121/3, 49/55, 3/77]

Vector representation:
```
-1  1  1  0  0
 2 -1  0 -1  0
 0 -1  0  0  2
 0  0 -1  2 -1
 0  1  0 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_302

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1,R1,R2 loop: from (2, b, c, d+k, e) to (2, b+k, c+2*k, d, e)
theorem r1r2_loop : ⟨2, b, c, d+k, e⟩ [fm]⊢* ⟨2, b+k, c+2*k, d, e⟩ := by
  have h : ∀ k b c, ⟨2, b, c, d+k, e⟩ [fm]⊢* ⟨2, b+k, c+2*k, d, e⟩ := by
    intro k; induction' k with k ih <;> intro b c
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h k b c

-- R3 phase: from (0, b+k, c, 0, e) to (0, b, c, 0, e+2*k)
theorem r3_loop : ⟨0, b+k, c, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e+2*k⟩ := by
  have h : ∀ k b e, ⟨0, b+k, c, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e+2*k⟩ := by
    intro k; induction' k with k ih <;> intro b e
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h k b e

-- R4 phase: from (0, 0, c+k, d, e+k) to (0, 0, c, d+2*k, e)
theorem r4_loop : ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+2*k, e⟩ := by
  have h : ∀ k c d e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+2*k, e⟩ := by
    intro k; induction' k with k ih <;> intro c d e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish
  exact h k c d e

-- Main transition: (0, 0, 0, D+2, E+1) →⁺ (0, 0, 0, 4*D+4, E+2)
theorem main_trans : ⟨0, 0, 0, D+2, E+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*D+4, E+2⟩ := by
  -- R5: (0, 0, 0, D+2, E+1) -> (0, 1, 0, D+1, E)
  -- R2: (0, 1, 0, D+1, E) -> (2, 0, 0, D, E)
  step fm; step fm
  -- R1,R1,R2 loop D times: (2, 0, 0, D, E) -> (2, D, 2*D, 0, E)
  rw [show D = 0 + D from by ring]
  apply stepStar_trans r1r2_loop
  simp only [Nat.zero_add]
  -- R1,R1: (2, D, 2*D, 0, E) -> (0, D+2, 2*D+2, 0, E)
  step fm; step fm
  -- R3 phase: (0, D+2, 2*D+2, 0, E) -> (0, 0, 2*D+2, 0, E+2*(D+2))
  rw [show D + 2 = 0 + (D + 2) from by ring]
  apply stepStar_trans r3_loop
  -- R4 phase: (0, 0, 2*D+2, 0, E+2*(D+2)) -> (0, 0, 0, 2*(2*D+2), E+2*(D+2)-(2*D+2))
  -- = (0, 0, 0, 4*D+4, E+2)
  -- c = 2*D+2, e = E + 2*D + 4
  -- We need: c + k = 2*D+2, e + k = E + 2*D + 4, so k = 2*D+2, c = 0, e = E+2
  rw [show (2 * D + 2 : ℕ) = 0 + (2 * D + 2) from by ring,
      show E + 2 * (D + 2) = (E + 2) + (2 * D + 2) from by ring]
  apply stepStar_trans r4_loop
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D + 2, E + 1⟩)
  · intro c ⟨D, E, hq⟩; subst hq
    refine ⟨⟨0, 0, 0, 4 * D + 4, E + 2⟩, ⟨4 * D + 2, E + 1, ?_⟩, main_trans⟩
    simp
  · exact ⟨0, 0, rfl⟩
