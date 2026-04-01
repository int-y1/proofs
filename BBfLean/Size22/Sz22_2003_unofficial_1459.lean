import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1459: [7/15, 3/77, 242/3, 5/11, 1617/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  1  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1459

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | _ => none

-- R3 chain: repeated R3 steps (c = 0, d = 0).
theorem r3_chain : ∀ k, ∀ a b e, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (e + 2))
    ring_nf; finish

-- R4 chain: repeated R4 steps (b = 0, d = 0).
theorem r4_chain : ∀ k, ∀ a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

-- Pump chain: from (A, B+1, 0, D, 0), uses strong induction on D.
-- Result: (A+B+1+D, 0, 0, 0, 2*B+2+D).
theorem pump_chain : ∀ D, ∀ A B, ⟨A, B + 1, 0, D, 0⟩ [fm]⊢* ⟨A + B + 1 + D, 0, 0, 0, 2 * B + 2 + D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B
  rcases D with _ | _ | D
  · -- D = 0: just R3 chain
    rw [show B + 1 = 0 + (B + 1) from by ring,
        show A + B + 1 + 0 = A + (B + 1) from by ring,
        show 2 * B + 2 + 0 = 0 + 2 * (B + 1) from by ring]
    exact r3_chain (B + 1) A 0 0
  · -- D = 1: R3, R2, then R3 chain
    step fm  -- R3
    step fm  -- R2
    rw [show B + 1 = 0 + (B + 1) from by ring,
        show A + B + 1 + 1 = A + 1 + (B + 1) from by ring,
        show 2 * B + 2 + 1 = 1 + 2 * (B + 1) from by ring]
    exact r3_chain (B + 1) (A + 1) 0 1
  · -- D + 2: one R3+R2+R2 round, then recurse
    step fm  -- R3
    step fm  -- R2
    rw [show D + 1 = D + 1 from rfl]
    step fm  -- R2
    rw [show B + 2 = (B + 1) + 1 from by ring]
    apply stepStar_trans (ih D (by omega) (A + 1) (B + 1))
    ring_nf; finish

-- Drain + R5 + R1 + R2 for odd case.
-- From (a+m+1, 0, 2m+1, d, 0), drain m rounds then R5+R1+R2.
-- Result: (a, 1, 0, d+3m+2, 0).
theorem drain_odd : ∀ m, ∀ a d, ⟨a + m + 1, 0, 2 * m + 1, d, 0⟩ [fm]⊢* ⟨a, 1, 0, d + 3 * m + 2, 0⟩ := by
  intro m; induction' m with m ih <;> intro a d
  · -- m = 0: (a+1, 0, 1, d, 0). R5, R1, R2.
    step fm  -- R5: (a, 1, 1, d+2, 1)
    step fm  -- R1: (a, 0, 0, d+3, 1)
    step fm  -- R2: (a, 1, 0, d+2, 0)
    ring_nf; finish
  · -- m+1: (a+m+2, 0, 2m+3, d, 0). One drain round, then IH.
    rw [show a + (m + 1) + 1 = (a + m + 1) + 1 from by ring,
        show 2 * (m + 1) + 1 = (2 * m + 1) + 2 from by ring]
    step fm  -- R5: (a+m+1, 1, 2m+1+2, d+2, 1)
    rw [show 2 * m + 1 + 2 = (2 * m + 1) + 2 from by ring]
    step fm  -- R1: (a+m+1, 0, 2m+1+1, d+3, 1)
    step fm  -- R2: (a+m+1, 1, 2m+1+1, d+2, 0)
    rw [show 2 * m + 1 + 1 = (2 * m + 1) + 1 from by ring]
    step fm  -- R1: (a+m+1, 0, 2m+1, d+3, 0)
    rw [show 2 * m + 1 = 2 * m + 1 from rfl]
    apply stepStar_trans (ih a (d + 3))
    ring_nf; finish

-- Drain + R5 + R2 for even case.
-- From (a+m+1, 0, 2*(m+1), d, 0), drain m+1 rounds then R5+R2.
-- Result: (a, 2, 0, d+3*(m+1)+1, 0).
theorem drain_even : ∀ m, ∀ a d, ⟨a + m + 1 + 1, 0, 2 * (m + 1), d, 0⟩ [fm]⊢* ⟨a, 2, 0, d + 3 * (m + 1) + 1, 0⟩ := by
  intro m; induction' m with m ih <;> intro a d
  · -- m = 0: (a+2, 0, 2, d, 0). R5, R1, R2, R1, R5, R2.
    step fm  -- R5: (a+1, 1, 2, d+2, 1)
    step fm  -- R1: (a+1, 0, 1, d+3, 1)
    step fm  -- R2: (a+1, 1, 1, d+2, 0)
    step fm  -- R1: (a+1, 0, 0, d+3, 0)
    step fm  -- R5: (a, 1, 0, d+5, 1)
    step fm  -- R2: (a, 2, 0, d+4, 0)
    ring_nf; finish
  · -- m+1: (a+m+3, 0, 2*(m+2), d, 0). One drain round, then IH.
    rw [show a + (m + 1) + 1 + 1 = (a + m + 1 + 1) + 1 from by ring,
        show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 from by ring]
    step fm  -- R5
    rw [show 2 * (m + 1) + 2 = (2 * (m + 1)) + 2 from by ring]
    step fm  -- R1
    step fm  -- R2
    rw [show 2 * (m + 1) + 1 = (2 * (m + 1)) + 1 from by ring]
    step fm  -- R1
    rw [show 2 * (m + 1) = 2 * (m + 1) from rfl]
    apply stepStar_trans (ih a (d + 3))
    ring_nf; finish

-- Transition for e odd: e = 2*m + 1.
theorem trans_odd (a m : ℕ) :
    ⟨a + m + 1, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨a + 3 * m + 3, 0, 0, 0, 3 * m + 4⟩ := by
  -- R4 first step for ⊢⁺
  apply step_stepStar_stepPlus
  · show fm ⟨a + m + 1, 0, 0, 0, 2 * m + 1⟩ = some ⟨a + m + 1, 0, 1, 0, 2 * m⟩
    simp [fm]
  -- R4 remaining steps
  apply stepStar_trans (r4_chain (2 * m) (a + m + 1) 1)
  -- Now at (a+m+1, 0, 1+2*m, 0, 0). Use drain_odd.
  rw [show 1 + 2 * m = 2 * m + 1 from by ring]
  apply stepStar_trans (drain_odd m a 0)
  -- Now at (a, 1, 0, 0+3*m+2, 0) = (a, 1, 0, 3*m+2, 0).
  rw [show (1 : ℕ) = 0 + 1 from rfl,
      show (0 + 3 * m + 2 : ℕ) = 3 * m + 2 from by omega,
      show a + 3 * m + 3 = a + 0 + 1 + (3 * m + 2) from by ring,
      show 3 * m + 4 = 2 * 0 + 2 + (3 * m + 2) from by ring]
  exact pump_chain (3 * m + 2) a 0

-- Transition for e even: e = 2*(m+1).
theorem trans_even (a m : ℕ) :
    ⟨a + m + 2, 0, 0, 0, 2 * (m + 1)⟩ [fm]⊢⁺ ⟨a + 3 * m + 6, 0, 0, 0, 3 * m + 8⟩ := by
  -- R4 first step for ⊢⁺
  apply step_stepStar_stepPlus
  · show fm ⟨a + m + 2, 0, 0, 0, 2 * (m + 1)⟩ = some ⟨a + m + 2, 0, 1, 0, 2 * m + 1⟩
    simp [fm]
  -- R4 remaining steps
  apply stepStar_trans (r4_chain (2 * m + 1) (a + m + 2) 1)
  -- Now at (a+m+2, 0, 1+(2*m+1), 0, 0) = (a+m+2, 0, 2*(m+1), 0, 0).
  rw [show 1 + (2 * m + 1) = 2 * (m + 1) from by ring,
      show a + m + 2 = a + m + 1 + 1 from by ring]
  -- Use drain_even
  apply stepStar_trans (drain_even m a 0)
  -- Now at (a, 2, 0, 0+3*(m+1)+1, 0).
  rw [show (2 : ℕ) = 1 + 1 from rfl,
      show (0 + 3 * (m + 1) + 1 : ℕ) = 3 * m + 4 from by omega,
      show a + 3 * m + 6 = a + 1 + 1 + (3 * m + 4) from by ring,
      show 3 * m + 8 = 2 * 1 + 2 + (3 * m + 4) from by ring]
  exact pump_chain (3 * m + 4) a 1

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩)
  · execute fm 6
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 5 ∧ a + 2 ≥ e)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- e even: e = m + m
      subst hm
      rw [show m + m = 2 * m from by ring] at *
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, a = j + k + 2 := ⟨a - k - 2, by omega⟩
      refine ⟨⟨j + 3 * k + 6, 0, 0, 0, 3 * k + 8⟩,
        ⟨j + 3 * k + 6, 3 * k + 8, rfl, by omega, by omega⟩, ?_⟩
      show ⟨j + k + 2, 0, 0, 0, 2 * (k + 1)⟩ [fm]⊢⁺ ⟨j + 3 * k + 6, 0, 0, 0, 3 * k + 8⟩
      exact trans_even j k
    · -- e odd: e = 2*m + 1
      subst hm
      obtain ⟨j, rfl⟩ : ∃ j, a = j + m + 1 := ⟨a - m - 1, by omega⟩
      refine ⟨⟨j + 3 * m + 3, 0, 0, 0, 3 * m + 4⟩,
        ⟨j + 3 * m + 3, 3 * m + 4, rfl, by omega, by omega⟩, ?_⟩
      exact trans_odd j m
  · exact ⟨3, 5, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1459
