import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #324: [18/35, 1/363, 5/3, 11/5, 147/2]

Vector representation:
```
 1  2 -1 -1  0
 0 -1  0  0 -2
 0 -1  1  0  0
 0  0 -1  0  1
-1  1  0  2  0
```

This Fractran program doesn't halt. The canonical state is (a, 0, 0, 0, e) with 2*a >= e+2.
Even e=2k maps to (a+k+1, 0, 0, 0, 2k+3); odd e=2k+1 maps to (a+k+1, 0, 0, 0, 2k+4).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_324

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- Drain a while consuming e in pairs (even): (a+k, 0, 0, D, 2k) →* (a, 0, 0, D+2k, 0)
theorem drain_even : ∀ k a D,
    ⟨a + k, 0, 0, D, 2 * k⟩ [fm]⊢* (⟨a, 0, 0, D + 2 * k, 0⟩ : Q) := by
  intro k; induction k with
  | zero => intro a D; exists 0
  | succ k ih =>
    intro a D
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
        show D + (2 * k + 1 + 1) = (D + 2) + 2 * k from by ring]
    step fm; step fm
    exact ih a (D + 2)

-- Drain a while consuming e in pairs (odd): (a+k, 0, 0, D, 2k+1) →* (a, 0, 0, D+2k, 1)
theorem drain_odd : ∀ k a D,
    ⟨a + k, 0, 0, D, 2 * k + 1⟩ [fm]⊢* (⟨a, 0, 0, D + 2 * k, 1⟩ : Q) := by
  intro k; induction k with
  | zero => intro a D; exists 0
  | succ k ih =>
    intro a D
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by ring,
        show D + 2 * (k + 1) = (D + 2) + 2 * k from by ring]
    step fm; step fm
    exact ih a (D + 2)

-- Climb with e=0: rule1 + rule3 loop
-- (A, B, 1, D+1, 0) →* (A+D+1, B+D+1, 1, 0, 0)
theorem climb_e0 : ∀ D A B,
    ⟨A, B, 1, D + 1, 0⟩ [fm]⊢* (⟨A + D + 1, B + D + 1, 1, 0, 0⟩ : Q) := by
  intro D; induction D with
  | zero =>
    intro A B; step fm; step fm
    rw [show A + 0 + 1 = A + 1 from by ring, show B + 0 + 1 = B + 1 from by ring]
    exists 0
  | succ D ih =>
    intro A B; step fm; step fm
    rw [show A + (D + 1) + 1 = (A + 1) + D + 1 from by ring,
        show B + (D + 1) + 1 = (B + 1) + D + 1 from by ring]
    exact ih (A + 1) (B + 1)

-- Climb with e=1
-- (A, B, 1, D+1, 1) →* (A+D+1, B+D+1, 1, 0, 1)
theorem climb_e1 : ∀ D A B,
    ⟨A, B, 1, D + 1, 1⟩ [fm]⊢* (⟨A + D + 1, B + D + 1, 1, 0, 1⟩ : Q) := by
  intro D; induction D with
  | zero =>
    intro A B; step fm; step fm
    rw [show A + 0 + 1 = A + 1 from by ring, show B + 0 + 1 = B + 1 from by ring]
    exists 0
  | succ D ih =>
    intro A B; step fm; step fm
    rw [show A + (D + 1) + 1 = (A + 1) + D + 1 from by ring,
        show B + (D + 1) + 1 = (B + 1) + D + 1 from by ring]
    exact ih (A + 1) (B + 1)

-- b-to-c with e=0: (A, B, C, 0, 0) →* (A, 0, B+C, 0, 0)
theorem b_to_c_e0 : ∀ B A C,
    ⟨A, B, C, 0, 0⟩ [fm]⊢* (⟨A, 0, B + C, 0, 0⟩ : Q) := by
  intro B; induction B with
  | zero => intro A C; simp; exists 0
  | succ B ih =>
    intro A C; step fm
    rw [show B + 1 + C = B + (C + 1) from by ring]
    exact ih A (C + 1)

-- b-to-c with e=1: (A, B, C, 0, 1) →* (A, 0, B+C, 0, 1)
theorem b_to_c_e1 : ∀ B A C,
    ⟨A, B, C, 0, 1⟩ [fm]⊢* (⟨A, 0, B + C, 0, 1⟩ : Q) := by
  intro B; induction B with
  | zero => intro A C; simp; exists 0
  | succ B ih =>
    intro A C; step fm
    rw [show B + 1 + C = B + (C + 1) from by ring]
    exact ih A (C + 1)

-- c-to-e: (A, 0, C, 0, E) →* (A, 0, 0, 0, E+C)
theorem c_to_e : ∀ C A E,
    ⟨A, 0, C, 0, E⟩ [fm]⊢* (⟨A, 0, 0, 0, E + C⟩ : Q) := by
  intro C; induction C with
  | zero => intro A E; exists 0
  | succ C ih =>
    intro A E; step fm
    rw [show E + (C + 1) = (E + 1) + C from by ring]
    exact ih A (E + 1)

-- Even cycle: (a+k+1, 0, 0, 0, 2k) ⊢⁺ (a+2k+2, 0, 0, 0, 2k+3)
theorem cycle_even (a k : ℕ) :
    ⟨a + k + 1, 0, 0, 0, 2 * k⟩ [fm]⊢⁺ (⟨a + 2 * k + 2, 0, 0, 0, 2 * k + 3⟩ : Q) := by
  rw [show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (h₁ := drain_even k (a + 1) 0)
  step fm; step fm
  rw [show 0 + 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  apply stepStar_trans (climb_e0 (2 * k + 1) a 0)
  rw [show a + (2 * k + 1) + 1 = a + 2 * k + 2 from by ring,
      show 0 + (2 * k + 1) + 1 = 2 * k + 2 from by ring]
  apply stepStar_trans (b_to_c_e0 (2 * k + 2) (a + 2 * k + 2) 1)
  rw [show 2 * k + 2 + 1 = 2 * k + 3 from by ring]
  apply stepStar_trans (c_to_e (2 * k + 3) (a + 2 * k + 2) 0)
  simp; exists 0

-- Odd cycle: (a+k+1, 0, 0, 0, 2k+1) ⊢⁺ (a+2k+2, 0, 0, 0, 2k+4)
theorem cycle_odd (a k : ℕ) :
    ⟨a + k + 1, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ (⟨a + 2 * k + 2, 0, 0, 0, 2 * k + 4⟩ : Q) := by
  rw [show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (h₁ := drain_odd k (a + 1) 0)
  step fm; step fm
  rw [show 0 + 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  apply stepStar_trans (climb_e1 (2 * k + 1) a 0)
  rw [show a + (2 * k + 1) + 1 = a + 2 * k + 2 from by ring,
      show 0 + (2 * k + 1) + 1 = 2 * k + 2 from by ring]
  apply stepStar_trans (b_to_c_e1 (2 * k + 2) (a + 2 * k + 2) 1)
  rw [show 2 * k + 2 + 1 = 2 * k + 3 from by ring]
  apply stepStar_trans (c_to_e (2 * k + 3) (a + 2 * k + 2) 1)
  rw [show 1 + (2 * k + 3) = 2 * k + 4 from by ring]
  exists 0

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 6⟩) (by execute fm 32)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a k, k ≥ 1 ∧
      (q = (⟨a + k + 1, 0, 0, 0, 2 * k⟩ : Q) ∨
       q = (⟨a + k + 1, 0, 0, 0, 2 * k + 1⟩ : Q)))
  · intro c ⟨a, k, hk, hq⟩
    rcases hq with hq | hq <;> subst hq
    · exact ⟨_, ⟨a + k, k + 1, by omega, Or.inr (by ring_nf)⟩, cycle_even a k⟩
    · have hk1 : a + k ≥ 1 := by omega
      refine ⟨_, ⟨a + k - 1, k + 2, by omega, Or.inl ?_⟩, cycle_odd a k⟩
      show _ = (a + k - 1 + (k + 2) + 1, 0, 0, 0, 2 * (k + 2))
      congr 1; omega
  · exact ⟨0, 3, by omega, Or.inl (by ring_nf)⟩

end Sz22_2003_unofficial_324
