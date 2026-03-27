import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #177: [1/45, 98/5, 125/77, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 1  0 -1  2  0
 0  0  3 -1 -1
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_177

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: d → b
theorem d_to_b : ∀ k b d, ⟨a, b, 0, d + k, (0 : ℕ)⟩ [fm]⊢* ⟨a, b + k, 0, d, (0 : ℕ)⟩ := by
  intro k; induction k with
  | zero => intro b d; exists 0
  | succ k ih =>
    intro b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Drain: repeated (R5, R1) pairs.
-- (A+k, B+2k, 0, 0, e) ⊢* (A, B, 0, 0, e+k)
theorem drain : ∀ k A B e, ⟨A + k, B + 2 * k, 0, 0, e⟩ [fm]⊢* ⟨A, B, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro A B e; simp; exists 0
  | succ k ih =>
    intro A B e
    rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring]
    -- R5
    step fm
    -- R1
    rw [show B + 2 * k + 2 = (B + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih A B (e + 1))
    ring_nf; finish

-- Build setup for b=1
theorem build_setup_1 (R E : ℕ) : ⟨R + 1, 1, 0, 0, E⟩ [fm]⊢* ⟨R + 4, (1 : ℕ), 0, 7, E⟩ := by
  step fm; step fm
  rw [show E + 1 = E + 1 from rfl]
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Build setup for b=0
theorem build_setup_0 (R E : ℕ) : ⟨R + 1, 0, 0, 0, E⟩ [fm]⊢* ⟨R + 4, (0 : ℕ), 0, 7, E⟩ := by
  step fm; step fm
  rw [show E + 1 = E + 1 from rfl]
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Build loop for b=1
theorem build_loop_1 : ∀ k A D, ⟨A, 1, 0, D + 1, k⟩ [fm]⊢* ⟨A + 3 * k, (1 : ℕ), 0, D + 5 * k + 1, (0 : ℕ)⟩ := by
  intro k; induction k with
  | zero => intro A D; exists 0
  | succ k ih =>
    intro A D
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Build loop for b=0
theorem build_loop_0 : ∀ k A D, ⟨A, 0, 0, D + 1, k⟩ [fm]⊢* ⟨A + 3 * k, (0 : ℕ), 0, D + 5 * k + 1, (0 : ℕ)⟩ := by
  intro k; induction k with
  | zero => intro A D; exists 0
  | succ k ih =>
    intro A D
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Full build for b=1
theorem build_1 (R E : ℕ) : ⟨R + 1, 1, 0, 0, E⟩ [fm]⊢* ⟨R + 3 * E + 4, (1 : ℕ), 0, 5 * E + 7, (0 : ℕ)⟩ := by
  apply stepStar_trans (build_setup_1 R E)
  have h := build_loop_1 E (R + 4) 6
  rw [show (6 : ℕ) + 5 * E + 1 = 5 * E + 7 from by ring,
      show R + 4 + 3 * E = R + 3 * E + 4 from by ring] at h
  exact h

-- Full build for b=0
theorem build_0 (R E : ℕ) : ⟨R + 1, 0, 0, 0, E⟩ [fm]⊢* ⟨R + 3 * E + 4, (0 : ℕ), 0, 5 * E + 7, (0 : ℕ)⟩ := by
  apply stepStar_trans (build_setup_0 R E)
  have h := build_loop_0 E (R + 4) 6
  rw [show (6 : ℕ) + 5 * E + 1 = 5 * E + 7 from by ring,
      show R + 4 + 3 * E = R + 3 * E + 4 from by ring] at h
  exact h

-- Main transition for odd B = 2k+1 where k ≥ 1:
-- (A+k+1, 2k+1, 0, 0, 0) ⊢⁺ (A+3k+4, 5k+8, 0, 0, 0)
-- We make the first step explicit for stepPlus.
theorem odd_trans (A k : ℕ) (hk : k ≥ 1) :
    ⟨A + k + 1, 2 * k + 1, 0, 0, (0 : ℕ)⟩ [fm]⊢⁺ ⟨A + 3 * k + 4, 5 * k + 8, 0, 0, (0 : ℕ)⟩ := by
  -- First step: R5 fires (a = A+k+1 ≥ 1)
  rw [show A + k + 1 = (A + k) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(A + k) + 1, 2 * k + 1, 0, 0, 0⟩ = some ⟨A + k, 2 * k + 1, 1, 0, 1⟩
    simp [fm]
  -- Now at (A+k, 2k+1, 1, 0, 1). R1 fires (b=2k+1≥2 since k≥1, c=1≥1)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 from by ring]
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨A + (j + 1), (2 * j + 1) + 2, 0 + 1, 0, 1⟩ = some ⟨A + (j + 1), 2 * j + 1, 0, 0, 1⟩ from by simp [fm])
  -- Now at (A+j+1, 2j+1, 0, 0, 1). Drain j more pairs.
  rw [show A + (j + 1) = (A + 1) + j from by ring,
      show 2 * j + 1 = 1 + 2 * j from by ring]
  apply stepStar_trans (drain j (A + 1) 1 1)
  rw [show 1 + j = j + 1 from by ring]
  -- Now at (A+1, 1, 0, 0, j+1). Build.
  rw [show A + 1 = A + 0 + 1 from by ring]
  apply stepStar_trans (build_1 A (j + 1))
  rw [show A + 3 * (j + 1) + 4 = A + 3 * (j + 1) + 4 from rfl]
  -- Now at (A+3j+7, 1, 0, 5j+12, 0). d_to_b.
  rw [show 5 * (j + 1) + 7 = 0 + (5 * (j + 1) + 7) from by ring]
  apply stepStar_trans (d_to_b (5 * (j + 1) + 7) 1 0 (a := A + 3 * (j + 1) + 4))
  rw [show (1 : ℕ) + (5 * (j + 1) + 7) = 5 * (j + 1) + 8 from by ring]
  ring_nf; finish

-- Main transition for even B = 2*(k+1):
-- (A+k+2, 2*(k+1), 0, 0, 0) ⊢⁺ (A+3k+7, 5k+12, 0, 0, 0)
theorem even_trans (A k : ℕ) :
    ⟨A + k + 2, 2 * (k + 1), 0, 0, (0 : ℕ)⟩ [fm]⊢⁺ ⟨A + 3 * k + 7, 5 * k + 12, 0, 0, (0 : ℕ)⟩ := by
  -- First step: R5
  rw [show A + k + 2 = (A + k + 1) + 1 from by ring,
      show 2 * (k + 1) = 2 * k + 2 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨(A + k + 1) + 1, 2 * k + 2, 0, 0, 0⟩ = some ⟨A + k + 1, 2 * k + 2, 1, 0, 1⟩
    simp [fm]
  -- R1: (A+k+1, (2k)+2, 0+1, 0, 1) → (A+k+1, 2k, 0, 0, 1)
  rw [show 2 * k + 2 = (2 * k) + 2 from by ring]
  apply stepStar_trans
  · exact step_stepStar (show fm ⟨A + k + 1, (2 * k) + 2, 0 + 1, 0, 1⟩ = some ⟨A + k + 1, 2 * k, 0, 0, 1⟩ from by simp [fm])
  -- Now at (A+k+1, 2k, 0, 0, 1). Drain k more pairs.
  rw [show A + k + 1 = (A + 1) + k from by ring,
      show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (drain k (A + 1) 0 1)
  rw [show 1 + k = k + 1 from by ring]
  -- Now at (A+1, 0, 0, 0, k+1). Build.
  rw [show A + 1 = A + 0 + 1 from by ring]
  apply stepStar_trans (build_0 A (k + 1))
  -- Now at (A+3k+7, 0, 0, 5k+12, 0). d_to_b.
  rw [show A + 3 * (k + 1) + 4 = A + 3 * k + 7 from by ring,
      show 5 * (k + 1) + 7 = 0 + (5 * k + 12) from by ring]
  apply stepStar_trans (d_to_b (5 * k + 12) 0 0 (a := A + 3 * k + 7))
  rw [show (0 : ℕ) + (5 * k + 12) = 5 * k + 12 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 7, 0, 0, 0⟩) (by execute fm 13)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦
      (∃ A k, k ≥ 1 ∧ q = ⟨A + k + 1, 2 * k + 1, 0, 0, (0 : ℕ)⟩) ∨
      (∃ A k, q = ⟨A + k + 2, 2 * (k + 1), 0, 0, (0 : ℕ)⟩))
  · intro c hP
    rcases hP with ⟨A, k, hk, rfl⟩ | ⟨A, k, rfl⟩
    · -- Odd case: (A+k+1, 2k+1) ⊢⁺ (A+3k+4, 5k+8)
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      refine ⟨⟨A + 3 * (j + 1) + 4, 5 * (j + 1) + 8, 0, 0, 0⟩, ?_, odd_trans A (j + 1) (by omega)⟩
      -- B' = 5j+13. Check parity of j+1:
      rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
      · -- j=2i: k=2i+1, B'=5(2i+1)+8=10i+13, odd.
        -- B'=2*(5i+6)+1, k'=5i+6≥1
        -- State: (A+6i+7, 10i+13, 0, 0, 0) = (m+k'+1, 2k'+1, 0, 0, 0)
        -- m = A+6i+7-(5i+6)-1 = A+i
        left; subst hi
        refine ⟨A + i, 5 * i + 6, by omega, ?_⟩
        ring_nf
      · -- j=2i+1: k=2i+2, B'=5(2i+2)+8=10i+18, even.
        -- B'=2*(5i+9), k'=5i+8
        -- State: (A+6i+10, 10i+18, 0, 0, 0) = (m+k'+2, 2*(k'+1), 0, 0, 0)
        -- m = A+6i+10-(5i+8)-2 = A+i
        right; subst hi
        refine ⟨A + i, 5 * i + 8, ?_⟩
        ring_nf
    · -- Even case: (A+k+2, 2*(k+1)) ⊢⁺ (A+3k+7, 5k+12)
      refine ⟨⟨A + 3 * k + 7, 5 * k + 12, 0, 0, 0⟩, ?_, even_trans A k⟩
      rcases Nat.even_or_odd k with ⟨i, hi⟩ | ⟨i, hi⟩
      · -- k=2i: B'=10i+12, even. B'=2*(5i+6), k'=5i+5
        -- State: (A+6i+7, 10i+12, 0, 0, 0) = (m+k'+2, 2*(k'+1), 0, 0, 0)
        -- m = A+6i+7-(5i+5)-2 = A+i
        right; subst hi
        refine ⟨A + i, 5 * i + 5, ?_⟩
        ring_nf
      · -- k=2i+1: B'=10i+17, odd. B'=2*(5i+8)+1, k'=5i+8≥1
        -- State: (A+6i+10, 10i+17, 0, 0, 0) = (m+k'+1, 2k'+1, 0, 0, 0)
        -- m = A+6i+10-(5i+8)-1 = A+i+1
        left; subst hi
        refine ⟨A + i + 1, 5 * i + 8, by omega, ?_⟩
        ring_nf
  · left; exact ⟨0, 3, by omega, by ring_nf⟩

end Sz22_2003_unofficial_177
