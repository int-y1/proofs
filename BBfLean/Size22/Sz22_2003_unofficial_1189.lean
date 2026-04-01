import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1189: [5/6, 49/2, 484/35, 3/11, 15/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  2
 0  1  0  0 -1
 0  1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1189

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: move e to b
theorem e_to_b : ∀ k, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [Nat.add_succ e k]; step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- One round of R3,R1,R1
theorem r3r1r1_step : ⟨(0 : ℕ), b + 2, c + 1, d + 1, e⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + 2, d, e + 2⟩ := by
  step fm; step fm; step fm; finish

-- k rounds of R3,R1,R1
theorem r3r1r1_chain : ∀ k, ∀ b c d e,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + 1 + k, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans r3r1r1_step
    apply stepStar_trans (ih b (c + 1) d (e + 2))
    ring_nf; finish

-- One round of R3,R2,R2
theorem r3r2r2_step : ⟨(0 : ℕ), 0, c + 1, d + 1, e⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, c, d + 4, e + 2⟩ := by
  step fm; step fm; step fm; finish

-- k rounds of R3,R2,R2
theorem r3r2r2_chain : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, c, d + 1 + 3 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    apply stepStar_trans r3r2r2_step
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 2))
    ring_nf; finish

-- Even E=2m transition: (0,0,0,D+m+2,2m) ⊢⁺ (0,0,0,D+3m+5,4m+4)
-- Phase 1: e_to_b → (0,2m,0,D+m+2,0)
-- Phase 2: R5 → (0,2m+1,1,D+m+1,0)
-- Phase 3: R3R1R1 x m → (0,1,m+1,D+1,2m)
-- Cleanup R3,R1,R2 → (0,0,m+1,D+2,2m+2) [only when m > 0]
-- Phase 4: R3R2R2 x (m+1) → (0,0,0,D+3m+5,4m+4)
-- For m=0: R5 → (0,1,1,D+1,0). R3 → (2,1,0,D,2). R1 → (1,0,1,D,2).
--   R2 → (0,0,1,D+2,2). R3R2R2 x 1 → (0,0,0,D+5,4).
theorem trans_even (D m : ℕ) :
    ⟨(0 : ℕ), 0, 0, D + m + 2, 2 * m⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, D + 3 * m + 5, 4 * m + 4⟩ := by
  -- Phase 1: e_to_b
  rw [show (2 * m : ℕ) = 0 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m) (b := 0) (d := D + m + 2) (e := 0))
  -- Now at (0, 2m, 0, D+m+2, 0). Phase 2: R5.
  step fm
  -- Now at (0, 0+2m+1, 1, D+m+1, 0). Phase 3: R3R1R1 x m.
  rw [show 0 + 2 * m + 1 = 1 + 2 * m from by ring,
      show D + m + 1 = (D + 1) + m from by ring]
  apply stepStar_trans (r3r1r1_chain m 1 0 (D + 1) 0)
  -- Now at (0, 1, 0+1+m, D+1, 0+2m) = (0, 1, m+1, D+1, 2m).
  -- Cleanup: R3 (needs c+1 and d+1), R1, R2
  rw [show 0 + 1 + m = m + 1 from by ring,
      show D + 1 = D + 1 from rfl,
      show 0 + 2 * m = 2 * m from by ring]
  -- State: (0, 1, m+1, D+1, 2m). R3: needs (m+1) as c+1 and (D+1) as d+1.
  -- m+1 = Nat.succ m = m+1. D+1 = Nat.succ D. Both successors.
  step fm  -- R3: (2, 1, m, D, 2m+2)
  step fm  -- R1: (1, 0, m+1, D, 2m+2)
  step fm  -- R2: (0, 0, m+1, D+2, 2m+2)
  -- Phase 4: R3R2R2 x (m+1). State: (0, 0, m+1, D+2, 2m+2).
  -- Need to match (0, 0, c+k, d+1, e). c=0, k=m+1, d+1=D+2.
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show D + 2 = (D + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 1) 0 (D + 1) (2 * m + 2))
  ring_nf; finish

-- Odd E=2m+1 transition: (0,0,0,D+m+3,2m+1) ⊢⁺ (0,0,0,D+3m+7,4m+6)
-- Phase 1: e_to_b → (0,2m+1,0,D+m+3,0)
-- Phase 2: R5 → (0,2m+2,1,D+m+2,0)
-- Phase 3: R3R1R1 x (m+1) → (0,0,m+2,D+1,2m+2)
-- Phase 4: R3R2R2 x (m+2) → (0,0,0,D+3m+7,4m+6)
theorem trans_odd (D m : ℕ) :
    ⟨(0 : ℕ), 0, 0, D + m + 3, 2 * m + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, D + 3 * m + 7, 4 * m + 6⟩ := by
  rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (2 * m + 1) (b := 0) (d := D + m + 3) (e := 0))
  step fm  -- R5: (0, 0+(2m+1)+1, 1, D+m+2, 0)
  rw [show 0 + (2 * m + 1) + 1 = 0 + 2 * (m + 1) from by ring,
      show D + m + 2 = (D + 1) + (m + 1) from by ring]
  apply stepStar_trans (r3r1r1_chain (m + 1) 0 0 (D + 1) 0)
  -- After chain: (0, 0, 0+1+(m+1), D+1, 0+2*(m+1)) = (0, 0, m+2, D+1, 2m+2)
  rw [show 0 + 1 + (m + 1) = 0 + (m + 2) from by ring,
      show D + 1 = (D + 0) + 1 from by ring,
      show 0 + 2 * (m + 1) = 2 * m + 2 from by ring]
  apply stepStar_trans (r3r2r2_chain (m + 2) 0 (D + 0) (2 * m + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ 2 ∧ 2 * D ≥ E + 4)
  · intro c ⟨D, E, hq, hD, hDE⟩; subst hq
    rcases Nat.even_or_odd E with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + m + 2 := ⟨D - m - 2, by omega⟩
      exact ⟨⟨0, 0, 0, D' + 3 * m + 5, 4 * m + 4⟩,
        ⟨D' + 3 * m + 5, 4 * m + 4, rfl, by omega, by omega⟩,
        trans_even D' m⟩
    · subst hm
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + m + 3 := ⟨D - m - 3, by omega⟩
      exact ⟨⟨0, 0, 0, D' + 3 * m + 7, 4 * m + 6⟩,
        ⟨D' + 3 * m + 7, 4 * m + 6, rfl, by omega, by omega⟩,
        trans_odd D' m⟩
  · exact ⟨2, 0, rfl, by omega, by omega⟩
