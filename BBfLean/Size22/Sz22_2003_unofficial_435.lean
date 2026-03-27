import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #435: [27/35, 22/5, 25/33, 7/11, 55/2]

Vector representation:
```
 0  3 -1 -1  0
 1  0 -1  0  1
 0 -1  2  0 -1
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_435

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- Rule 4 repeated: transfer e to d
theorem e_to_d : ⟨a, 0, 0, d, e + k⟩ [fm]⊢* (⟨a, 0, 0, d + k, e⟩ : Q) := by
  have h : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* (⟨a, 0, 0, d + k, e⟩ : Q) := by
    intro k; induction k with
    | zero => intro d; exists 0
    | succ k ih =>
      intro d
      rw [show e + (k + 1) = (e + k) + 1 from by ring]
      step fm
      apply stepStar_trans (ih (d + 1))
      ring_nf; finish
  exact h k d

-- Macro1 loop: (a+k, b, 0, d+3*k, 0) ->* (a, b+8*k, 0, d, 0)
-- Each iteration: 5 fixed steps consuming 1a and 3d, producing 8b
theorem macro1_loop : ⟨a + k, b, 0, d + 3 * k, 0⟩ [fm]⊢* (⟨a, b + 8 * k, 0, d, 0⟩ : Q) := by
  have h : ∀ k a b d, ⟨a + k, b, 0, d + 3 * k, 0⟩ [fm]⊢* (⟨a, b + 8 * k, 0, d, 0⟩ : Q) := by
    intro k; induction k with
    | zero => intro a b d; simp; exists 0
    | succ k ih =>
      intro a b d
      rw [show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring,
          show a + (k + 1) = (a + 1) + k from by ring]
      refine stepStar_trans (ih (a + 1) b (d + 3)) ?_
      rw [show b + 8 * (k + 1) = b + 8 * k + 8 from by ring]
      execute fm 5
  exact h k a b d

-- b_consume: each b gives +2 to a, +1 to e (rule3, rule2, rule2)
theorem b_consume : ⟨a, b + k, 0, 0, e + 1⟩ [fm]⊢* (⟨a + 2 * k, b, 0, 0, e + 1 + k⟩ : Q) := by
  have h : ∀ k a e, ⟨a, b + k, 0, 0, e + 1⟩ [fm]⊢* (⟨a + 2 * k, b, 0, 0, e + 1 + k⟩ : Q) := by
    intro k; induction k with
    | zero => intro a e; simp; exists 0
    | succ k ih =>
      intro a e
      rw [show b + (k + 1) = (b + k) + 1 from by ring,
          show e + 1 = (e + 0) + 1 from by ring]
      step fm; step fm; step fm
      apply stepStar_trans (ih (a + 2) (e + 1))
      ring_nf; finish
  exact h k a e

-- Full d=0 transition: (a+1, B, 0, 0, 0) ->⁺ (a+2*B+1, 0, 0, B+2, 0)
theorem d0_trans : ⟨a + 1, B, 0, 0, 0⟩ [fm]⊢⁺ (⟨a + 2 * B + 1, 0, 0, B + 2, 0⟩ : Q) := by
  step fm; step fm
  -- After step normalization we should be at (a+1, B, 0, 0, 2)
  -- b_consume needs form (_, 0+B, 0, 0, _+1). Use show to coerce.
  show (⟨a + 1, B, 0, 0, 2⟩ : Q) [fm]⊢* _
  rw [show (a + 1 : ℕ) = a + 1 from rfl,
      show (B : ℕ) = 0 + B from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (@b_consume (a + 1) 0 B 1)
  rw [show (1 : ℕ) + 1 + B = 0 + (B + 2) from by ring]
  apply stepStar_trans (@e_to_d (a + 1 + 2 * B) 0 0 (B + 2))
  ring_nf; finish

-- Full d=1 transition: (a+1, B, 0, 1, 0) ->⁺ (a+2*B+6, 0, 0, B+4, 0)
theorem d1_trans : ⟨a + 1, B, 0, 1, 0⟩ [fm]⊢⁺ (⟨a + 2 * B + 6, 0, 0, B + 4, 0⟩ : Q) := by
  step fm; step fm; step fm; step fm; step fm
  show (⟨a + 1 + 1, B + 2, 0, 0, 2⟩ : Q) [fm]⊢* _
  rw [show (B + 2 : ℕ) = 0 + (B + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (@b_consume (a + 1 + 1) 0 (B + 2) 1)
  rw [show (1 : ℕ) + 1 + (B + 2) = 0 + (B + 4) from by ring]
  apply stepStar_trans (@e_to_d (a + 1 + 1 + 2 * (B + 2)) 0 0 (B + 4))
  ring_nf; finish

-- Full d=2 transition: (a+1, B, 0, 2, 0) ->⁺ (a+2*B+11, 0, 0, B+6, 0)
theorem d2_trans : ⟨a + 1, B, 0, 2, 0⟩ [fm]⊢⁺ (⟨a + 2 * B + 11, 0, 0, B + 6, 0⟩ : Q) := by
  step fm; step fm; step fm; step fm; step fm
  -- After 5 steps: (a+1, B+4+1, 0, 0, 1) -- Lean normalizes B+5 as B+4+1? or B+5?
  -- We need to get into form for rule3 (b+1, e+1) then continue
  show (⟨a + 1, B + 4 + 1, 0, 0, 1⟩ : Q) [fm]⊢* _
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm
  show (⟨a + 1 + 1 + 1, B + 4, 0, 0, 2⟩ : Q) [fm]⊢* _
  rw [show (B + 4 : ℕ) = 0 + (B + 4) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (@b_consume (a + 1 + 1 + 1) 0 (B + 4) 1)
  rw [show (1 : ℕ) + 1 + (B + 4) = 0 + (B + 6) from by ring]
  apply stepStar_trans (@e_to_d (a + 1 + 1 + 1 + 2 * (B + 4)) 0 0 (B + 6))
  ring_nf; finish

-- Combined transitions
theorem mod0_trans : ⟨a + k + 2, 0, 0, 3 * (k + 1), 0⟩ [fm]⊢⁺
    (⟨a + 16 * k + 17, 0, 0, 8 * k + 10, 0⟩ : Q) := by
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring,
      show 3 * (k + 1) = 0 + 3 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (macro1_loop (d := 0))
  rw [show (0 : ℕ) + 8 * (k + 1) = 8 * k + 8 from by ring]
  have h := @d0_trans a (8 * k + 8)
  rw [show a + 2 * (8 * k + 8) + 1 = a + 16 * k + 17 from by ring,
      show 8 * k + 8 + 2 = 8 * k + 10 from by ring] at h
  exact h

theorem mod1_trans : ⟨a + k + 2, 0, 0, 3 * (k + 1) + 1, 0⟩ [fm]⊢⁺
    (⟨a + 16 * k + 22, 0, 0, 8 * k + 12, 0⟩ : Q) := by
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring,
      show 3 * (k + 1) + 1 = 1 + 3 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (macro1_loop (d := 1))
  rw [show (0 : ℕ) + 8 * (k + 1) = 8 * k + 8 from by ring]
  have h := @d1_trans a (8 * k + 8)
  rw [show a + 2 * (8 * k + 8) + 6 = a + 16 * k + 22 from by ring,
      show 8 * k + 8 + 4 = 8 * k + 12 from by ring] at h
  exact h

theorem mod2_trans : ⟨a + k + 2, 0, 0, 3 * (k + 1) + 2, 0⟩ [fm]⊢⁺
    (⟨a + 16 * k + 27, 0, 0, 8 * k + 14, 0⟩ : Q) := by
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring,
      show 3 * (k + 1) + 2 = 2 + 3 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (macro1_loop (d := 2))
  rw [show (0 : ℕ) + 8 * (k + 1) = 8 * k + 8 from by ring]
  have h := @d2_trans a (8 * k + 8)
  rw [show a + 2 * (8 * k + 8) + 11 = a + 16 * k + 27 from by ring,
      show 8 * k + 8 + 6 = 8 * k + 14 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨11, 0, 0, 6, 0⟩)
  · execute fm 30
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 3 ∧ 3 * a > d)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    have hmod : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · obtain ⟨K, rfl⟩ : ∃ K, d = 3 * K := ⟨d / 3, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      exact ⟨⟨m + 16 * k + 17, 0, 0, 8 * k + 10, 0⟩,
        ⟨m + 16 * k + 17, 8 * k + 10, rfl, by omega, by omega⟩, mod0_trans⟩
    · obtain ⟨K, rfl⟩ : ∃ K, d = 3 * K + 1 := ⟨d / 3, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      exact ⟨⟨m + 16 * k + 22, 0, 0, 8 * k + 12, 0⟩,
        ⟨m + 16 * k + 22, 8 * k + 12, rfl, by omega, by omega⟩, mod1_trans⟩
    · obtain ⟨K, rfl⟩ : ∃ K, d = 3 * K + 2 := ⟨d / 3, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      exact ⟨⟨m + 16 * k + 27, 0, 0, 8 * k + 14, 0⟩,
        ⟨m + 16 * k + 27, 8 * k + 14, rfl, by omega, by omega⟩, mod2_trans⟩
  · exact ⟨11, 6, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_435
