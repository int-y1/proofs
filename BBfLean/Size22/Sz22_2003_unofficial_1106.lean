import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1106: [5/6, 4/35, 539/2, 3/11, 5/7, 1/5]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0  0 -1
 0  0  1 -1  0
 0  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1106

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+2k, e+k)
theorem r3_chain : ∀ k, ∀ d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (d + 2) (e + 1)); ring_nf; finish

-- R4 chain: (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem r4_chain : ∀ k, ∀ b d, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

-- Spiral core: R1,R1,R2 repeated j times.
-- (2, b+2j, c, d+j, 0) →* (2, b, c+j, d, 0)
theorem spiral_core : ∀ j, ∀ b c d, ⟨2, b + 2 * j, c, d + j, 0⟩ [fm]⊢* ⟨2, b, c + j, d, 0⟩ := by
  intro j; induction' j with j ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (j + 1) = (b + 2) + 2 * j from by ring,
        show d + (j + 1) = (d + 1) + j from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1))
    step fm; step fm; step fm; finish

-- R2 drain: (a, 0, c+k, d+k, 0) →* (a+2k, 0, c, d, 0)
theorem r2_drain : ∀ k, ∀ a c d, ⟨a, 0, c + k, d + k, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d); ring_nf; finish

-- Phase 1+2: R3 drains a, R4 moves e to b.
-- (A, 0, 0, D, 0) →* (0, A, 0, D+2A, 0)
theorem phases12 (A D : ℕ) : ⟨A, 0, 0, D, 0⟩ [fm]⊢* ⟨0, A, 0, D + 2 * A, 0⟩ := by
  rw [show (A : ℕ) = 0 + A from by omega]
  apply stepStar_trans (r3_chain A (a := 0) (d := D) (e := 0))
  rw [show (0 : ℕ) + A = 0 + A from by omega]
  apply stepStar_trans (r4_chain A (e := 0) (b := 0) (d := D + 2 * A))
  ring_nf; finish

-- Phase 3-6 as ⊢⁺: R5, R2, spiral, R1, R2 drain.
-- (0, 2J+1, 0, D+2J+3, 0) ⊢⁺ (2J+3, 0, 0, D, 0)
theorem phases3456 (J D : ℕ) :
    ⟨0, 2 * J + 1, 0, D + 2 * J + 3, 0⟩ [fm]⊢⁺ ⟨2 * J + 3, 0, 0, D, 0⟩ := by
  -- R5: (0, 2J+1, 1, D+2J+2, 0)
  step fm
  -- R2: (2, 2J+1, 0, D+2J+1, 0)
  step fm
  -- Spiral core: j=J rounds
  rw [show 2 * J + 1 = 1 + 2 * J from by ring,
      show D + 2 * J + 1 = (D + J + 1) + J from by ring]
  apply stepStar_trans (spiral_core J (b := 1) (c := 0) (d := D + J + 1))
  -- State: (2, 1, 0+J, D+J+1, 0)
  -- R1: (1, 0, J+1, D+J+1, 0)
  rw [show (0 : ℕ) + J = J from by omega]; step fm
  -- R2 drain: k = J+1
  rw [show J + 1 = 0 + (J + 1) from by omega,
      show D + J + 1 = D + (J + 1) from by ring]
  apply stepStar_trans (r2_drain (J + 1) (a := 1) (c := 0) (d := D))
  ring_nf; finish

-- Main transition: (2k+5, 0, 0, k²+2k, 0) ⊢⁺ (2k+7, 0, 0, k²+4k+3, 0)
theorem main_transition (k : ℕ) :
    ⟨2 * k + 5, 0, 0, k ^ 2 + 2 * k, 0⟩ [fm]⊢⁺ ⟨2 * k + 7, 0, 0, k ^ 2 + 4 * k + 3, 0⟩ := by
  -- Phases 1+2: (2k+5, 0, 0, k²+2k, 0) →* (0, 2k+5, 0, k²+6k+10, 0)
  apply stepStar_stepPlus_stepPlus (phases12 (2 * k + 5) (k ^ 2 + 2 * k))
  -- Phases 3-6 with J = k+2:
  -- 2J+1 = 2k+5, D+2J+3 = k²+6k+10 → D = k²+4k+3-2? No.
  -- D + 2*(k+2) + 3 = k²+6k+10 → D = k²+6k+10 - 2k-4-3 = k²+4k+3
  -- 2J+3 = 2(k+2)+3 = 2k+7 ✓
  rw [show k ^ 2 + 2 * k + 2 * (2 * k + 5) = (k ^ 2 + 4 * k + 3) + 2 * (k + 2) + 3 from by ring,
      show 2 * k + 5 = 2 * (k + 2) + 1 from by ring]
  exact phases3456 (k + 2) (k ^ 2 + 4 * k + 3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩)
  · execute fm 20
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k, q = ⟨2 * k + 5, 0, 0, k ^ 2 + 2 * k, 0⟩)
  · intro c ⟨k, hq⟩; subst hq
    exact ⟨⟨2 * k + 7, 0, 0, k ^ 2 + 4 * k + 3, 0⟩,
      ⟨k + 1, by ring_nf⟩, main_transition k⟩
  · exact ⟨0, by simp⟩

end Sz22_2003_unofficial_1106
