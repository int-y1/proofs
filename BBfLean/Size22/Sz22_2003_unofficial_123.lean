import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #123: [1/405, 98/15, 3/7, 25/2, 3/5]

Vector representation:
```
 0 -4 -1  0
 1 -1 -1  2
 0  1  0 -1
-1  0  2  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_123

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+4, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R3 repeated: move d to b. (a, b, 0, d+k) →* (a, b+k, 0, d).
-- c must be 0 so rules 1,2 don't fire; b is free since rule 3 doesn't need b.
theorem d_to_b : ∀ k, ⟨a, b, 0, d + k⟩ [fm]⊢* ⟨a, b + k, 0, d⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R4 repeated: convert a to c. (a, 0, c, 0) →* (0, 0, c+2*a, 0).
-- b and d must be 0, c is free.
theorem r4_chain : ∀ a, ⟨a, 0, c, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * a, 0⟩ := by
  intro a; induction' a with a ih generalizing c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

-- Spiral phase: R3+R2 interleaving.
-- From (a, 0, n+1, d+1): R3 fires (d >= 1), then R2 fires (b >= 1, c >= 1).
-- Each cycle: a += 1, c -= 1, d += 1. After n+1 cycles we'd need c = 0.
-- Actually: (a, 0, n, d+1) →* (a+n, 0, 0, d+n+1).
-- But step fm needs to see the pattern. The first step: (a, 0, n, d+1).
-- R1: needs b >= 4, NO. R2: needs b >= 1, NO. R3: needs d >= 1, YES.
-- So R3 fires: (a, 1, n, d). Then with b=1:
-- If n >= 1: R2 fires (b=1, c=n >= 1): (a+1, 0, n-1, d+2).
-- If n = 0: R4 or R5 fires.
-- So the spiral needs n >= 1 at each step.
theorem spiral : ∀ n, ⟨a, 0, n, d + 1⟩ [fm]⊢* ⟨a + n, 0, 0, d + n + 1⟩ := by
  intro n; induction' n with n ih generalizing a d
  · exists 0
  · step fm  -- R3: (a, 1, n+1, d)
    step fm  -- R2: (a+1, 0, n, d+2)
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (d := d + 1))
    ring_nf; finish

-- Double R1 + R4: (a+1, b+8, 2, 0) →⁺ (a, b, 2, 0) [3 steps]
theorem double_R1_R4 : ⟨a + 1, b + 8, 2, 0⟩ [fm]⊢⁺ ⟨a, b, 2, 0⟩ := by
  step fm; step fm; step fm; finish

-- Double R1 loop by induction
theorem double_R1_loop : ∀ k, ⟨a + k, b + 8 * k, 2, 0⟩ [fm]⊢* ⟨a, b, 2, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show b + 8 * (k + 1) = (b + 8) + 8 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b + 8))
    exact stepPlus_stepStar double_R1_R4

-- End case B=1: (a, 1, 2, 0) →⁺ (a+2, 0, 0, 3) [3 steps]
theorem end_b1 : ⟨a, 1, 2, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 3⟩ := by
  step fm; step fm; step fm; finish

-- End case B=2: (a, 2, 2, 0) →⁺ (a+2, 0, 0, 4) [2 steps]
theorem end_b2 : ⟨a, 2, 2, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 4⟩ := by
  step fm; step fm; finish

-- End case B=3: (a, 3, 2, 0) →⁺ (a+2, 0, 0, 2) [9 steps]
theorem end_b3 : ⟨a, 3, 2, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 2⟩ := by
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; finish

-- End case B=5: (a, 5, 2, 0) →⁺ (a+1, 0, 0, 2) [2 steps]
theorem end_b5 : ⟨a, 5, 2, 0⟩ [fm]⊢⁺ ⟨a + 1, 0, 0, 2⟩ := by
  step fm; step fm; finish

-- End case B=6: (a, 6, 2, 0) →⁺ (a+2, 0, 0, 2) [14 steps]
theorem end_b6 : ⟨a, 6, 2, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 2⟩ := by
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; finish

-- End case B=4: (a, 4, 2, 0) →⁺ (a, 0, 1, 0) [1 step]
theorem end_b4 : ⟨a, 4, 2, 0⟩ [fm]⊢⁺ ⟨a, 0, 1, 0⟩ := by
  step fm; finish

-- End case B=7: (a, 7, 2, 0) →⁺ (a, 0, 1, 0) [6 steps]
theorem end_b7 : ⟨a, 7, 2, 0⟩ [fm]⊢⁺ ⟨a, 0, 1, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- (a+1, 0, 1, 0) → r4_chain → (0, 0, 2a+3, 0) → R5+R2+spiral → (2a+2, 0, 0, 2a+3)
theorem r4_to_spiral : ⟨a + 1, 0, 1, 0⟩ [fm]⊢* ⟨2 * a + 2, 0, 0, 2 * a + 3⟩ := by
  apply stepStar_trans (r4_chain (a + 1) (c := 1))
  rw [show 1 + 2 * (a + 1) = 2 * a + 3 from by ring]
  step fm  -- R5: (0, 1, 2*a+2, 0)
  step fm  -- R2: (1, 0, 2*a+1, 2)
  show ⟨1, 0, 2 * a + 1, 0 + 1 + 1⟩ [fm]⊢* ⟨2 * a + 2, 0, 0, 2 * a + 3⟩
  apply stepStar_trans (spiral (2 * a + 1) (a := 1) (d := 0 + 1))
  ring_nf; finish

-- (a, 0, 2, 0) → r4_chain → (0, 0, 2a+2, 0) → R5+R2+spiral → (2a+1, 0, 0, 2a+2)
theorem r4_chain_spiral2 : ⟨a, 0, 2, 0⟩ [fm]⊢* ⟨2 * a + 1, 0, 0, 2 * a + 2⟩ := by
  apply stepStar_trans (r4_chain a (c := 2))
  rw [show 2 + 2 * a = 2 * a + 2 from by ring]
  step fm  -- R5
  step fm  -- R2
  show ⟨1, 0, 2 * a, 0 + 1 + 1⟩ [fm]⊢* ⟨2 * a + 1, 0, 0, 2 * a + 2⟩
  apply stepStar_trans (spiral (2 * a) (a := 1) (d := 0 + 1))
  ring_nf; finish

-- D=2 transition: (a+2, 0, 0, 2) →⁺ (a+3, 0, 0, 4) [5 steps]
theorem d2_trans : ⟨a + 2, 0, 0, 2⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 4⟩ := by
  execute fm 5

-- D=3 transition: (a+3, 0, 0, 3) →⁺ (a+4, 0, 0, 2) [13 steps]
theorem d3_trans : ⟨a + 3, 0, 0, 3⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 2⟩ := by
  execute fm 13

-- D=5 transition: (a+4, 0, 0, 5) →⁺ (a+4, 0, 0, 2) [8 steps]
theorem d5_trans : ⟨a + 4, 0, 0, 5⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 2⟩ := by
  execute fm 8

-- D=4 transition: (a+3, 0, 0, 4) →⁺ (2a+4, 0, 0, 2a+5)
theorem d4_trans : ⟨a + 3, 0, 0, 4⟩ [fm]⊢⁺ ⟨2 * a + 4, 0, 0, 2 * a + 5⟩ := by
  step fm; step fm; step fm; step fm  -- R3 x 4
  step fm  -- R4
  step fm  -- R1: now at (a+2, 0, 1, 0)
  apply stepStar_trans (r4_to_spiral (a := a + 1))
  ring_nf; finish

-- Combined d_to_b + R4: (a+1, 0, 0, D) →⁺ (a, D, 2, 0)
-- d_to_b gives (a+1, D, 0, 0). Then R4 fires: (a, D, 2, 0).
theorem d_to_b_R4 : ∀ D, ⟨a + 1, 0, 0, D⟩ [fm]⊢⁺ ⟨a, D, 2, 0⟩ := by
  intro D
  apply stepStar_step_stepPlus
  · rw [show (D : ℕ) = 0 + D from by ring]
    exact d_to_b D (a := a + 1) (b := 0) (d := 0)
  · simp only [Nat.zero_add]
    simp [fm]

-- Even D = 8*n+2: (m+4*n+2, 0, 0, 8*n+2) →⁺ (m+3*n+3, 0, 0, 4)
theorem even_k0 : ⟨m + 4 * n + 2, 0, 0, 8 * n + 2⟩ [fm]⊢⁺ ⟨m + 3 * n + 3, 0, 0, 4⟩ := by
  rw [show m + 4 * n + 2 = (m + 4 * n + 1) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus (d_to_b_R4 (8 * n + 2))
  rw [show m + 4 * n + 1 = (m + 3 * n + 1) + n from by omega,
      show 8 * n + 2 = 2 + 8 * n from by ring]
  apply stepStar_trans (double_R1_loop n)
  exact stepPlus_stepStar end_b2

-- Even D = 8*n+4: (m+4*n+3, 0, 0, 8*n+4) →⁺ (2m+6n+4, 0, 0, 2m+6n+5)
theorem even_k1 : ⟨m + 4 * n + 3, 0, 0, 8 * n + 4⟩ [fm]⊢⁺ ⟨2 * m + 6 * n + 4, 0, 0, 2 * m + 6 * n + 5⟩ := by
  rw [show m + 4 * n + 3 = (m + 4 * n + 2) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus (d_to_b_R4 (8 * n + 4))
  rw [show m + 4 * n + 2 = (m + 3 * n + 2) + n from by omega,
      show 8 * n + 4 = 4 + 8 * n from by ring]
  apply stepStar_trans (double_R1_loop n)
  apply stepStar_trans (stepPlus_stepStar end_b4)
  apply stepStar_trans (r4_to_spiral (a := m + 3 * n + 1))
  ring_nf; finish

-- Even D = 8*n+6: (m+4*n+4, 0, 0, 8*n+6) →⁺ (m+3*n+5, 0, 0, 2)
theorem even_k2 : ⟨m + 4 * n + 4, 0, 0, 8 * n + 6⟩ [fm]⊢⁺ ⟨m + 3 * n + 5, 0, 0, 2⟩ := by
  rw [show m + 4 * n + 4 = (m + 4 * n + 3) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus (d_to_b_R4 (8 * n + 6))
  rw [show m + 4 * n + 3 = (m + 3 * n + 3) + n from by omega,
      show 8 * n + 6 = 6 + 8 * n from by ring]
  apply stepStar_trans (double_R1_loop n)
  exact stepPlus_stepStar end_b6

-- Even D = 8*(n+1): (m+4*n+5, 0, 0, 8*(n+1)) →⁺ (2m+6n+7, 0, 0, 2m+6n+8)
theorem even_k3 : ⟨m + 4 * n + 5, 0, 0, 8 * (n + 1)⟩ [fm]⊢⁺ ⟨2 * m + 6 * n + 7, 0, 0, 2 * m + 6 * n + 8⟩ := by
  rw [show m + 4 * n + 5 = (m + 4 * n + 4) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus (d_to_b_R4 (8 * (n + 1)))
  rw [show m + 4 * n + 4 = (m + 3 * n + 3) + (n + 1) from by omega,
      show 8 * (n + 1) = 0 + 8 * (n + 1) from by ring]
  apply stepStar_trans (double_R1_loop (n + 1))
  apply stepStar_trans (r4_chain_spiral2 (a := m + 3 * n + 3))
  ring_nf; finish

-- Odd D = 8*n+1: (m+4*n+1, 0, 0, 8*n+1) →⁺ (m+3*n+2, 0, 0, 3)
theorem odd_j0 : ⟨m + 4 * n + 1, 0, 0, 8 * n + 1⟩ [fm]⊢⁺ ⟨m + 3 * n + 2, 0, 0, 3⟩ := by
  rw [show m + 4 * n + 1 = (m + 4 * n) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus (d_to_b_R4 (8 * n + 1))
  rw [show m + 4 * n = (m + 3 * n) + n from by omega,
      show 8 * n + 1 = 1 + 8 * n from by ring]
  apply stepStar_trans (double_R1_loop n)
  exact stepPlus_stepStar end_b1

-- Odd D = 8*n+3: (m+4*n+3, 0, 0, 8*n+3) →⁺ (m+3*n+4, 0, 0, 2)
theorem odd_j1 : ⟨m + 4 * n + 3, 0, 0, 8 * n + 3⟩ [fm]⊢⁺ ⟨m + 3 * n + 4, 0, 0, 2⟩ := by
  rw [show m + 4 * n + 3 = (m + 4 * n + 2) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus (d_to_b_R4 (8 * n + 3))
  rw [show m + 4 * n + 2 = (m + 3 * n + 2) + n from by omega,
      show 8 * n + 3 = 3 + 8 * n from by ring]
  apply stepStar_trans (double_R1_loop n)
  exact stepPlus_stepStar end_b3

-- Odd D = 8*n+5: (m+4*n+4, 0, 0, 8*n+5) →⁺ (m+3*n+4, 0, 0, 2)
theorem odd_j2 : ⟨m + 4 * n + 4, 0, 0, 8 * n + 5⟩ [fm]⊢⁺ ⟨m + 3 * n + 4, 0, 0, 2⟩ := by
  rw [show m + 4 * n + 4 = (m + 4 * n + 3) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus (d_to_b_R4 (8 * n + 5))
  rw [show m + 4 * n + 3 = (m + 3 * n + 3) + n from by omega,
      show 8 * n + 5 = 5 + 8 * n from by ring]
  apply stepStar_trans (double_R1_loop n)
  exact stepPlus_stepStar end_b5

-- Odd D = 8*n+7: (m+4*n+5, 0, 0, 8*n+7) →⁺ (2m+6n+8, 0, 0, 2m+6n+9)
theorem odd_j3 : ⟨m + 4 * n + 5, 0, 0, 8 * n + 7⟩ [fm]⊢⁺ ⟨2 * m + 6 * n + 8, 0, 0, 2 * m + 6 * n + 9⟩ := by
  rw [show m + 4 * n + 5 = (m + 4 * n + 4) + 1 from by omega]
  apply stepPlus_stepStar_stepPlus (d_to_b_R4 (8 * n + 7))
  rw [show m + 4 * n + 4 = (m + 3 * n + 4) + n from by omega,
      show 8 * n + 7 = 7 + 8 * n from by ring]
  apply stepStar_trans (double_R1_loop n)
  apply stepStar_trans (stepPlus_stepStar end_b7)
  apply stepStar_trans (r4_to_spiral (a := m + 3 * n + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2⟩)
  · execute fm 32
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d⟩ ∧ d ≥ 2 ∧ 2 * a ≥ d + 2)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    rcases (show d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d ≥ 6 from by omega) with
      rfl | rfl | rfl | rfl | hd6
    · -- d = 2
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
      exact ⟨⟨m + 3, 0, 0, 4⟩, ⟨m + 3, 4, rfl, by omega, by omega⟩, d2_trans⟩
    · -- d = 3
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 3 := ⟨a - 3, by omega⟩
      exact ⟨⟨m + 4, 0, 0, 2⟩, ⟨m + 4, 2, rfl, by omega, by omega⟩, d3_trans⟩
    · -- d = 4
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 3 := ⟨a - 3, by omega⟩
      exact ⟨⟨2 * m + 4, 0, 0, 2 * m + 5⟩,
        ⟨2 * m + 4, 2 * m + 5, rfl, by omega, by omega⟩, d4_trans⟩
    · -- d = 5
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 4 := ⟨a - 4, by omega⟩
      exact ⟨⟨m + 4, 0, 0, 2⟩, ⟨m + 4, 2, rfl, by omega, by omega⟩, d5_trans⟩
    · -- d >= 6
      rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
      · -- d even: d = 2*K
        rw [show K + K = 2 * K from by ring] at hK; subst hK
        obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
        -- d = 2*(k+1), k >= 2
        obtain ⟨n, rfl | rfl | rfl | rfl⟩ : ∃ n, k = 4 * n ∨ k = 4 * n + 1 ∨ k = 4 * n + 2 ∨ k = 4 * n + 3 :=
          ⟨k / 4, by omega⟩
        · -- k = 4*n: d = 2*(4*n+1) = 8*n+2
          obtain ⟨m', rfl⟩ : ∃ m', a = m' + (4 * n + 2) := ⟨a - (4 * n + 2), by omega⟩
          refine ⟨⟨m' + 3 * n + 3, 0, 0, 4⟩,
            ⟨m' + 3 * n + 3, 4, rfl, by omega, by omega⟩, ?_⟩
          show ⟨m' + 4 * n + 2, 0, 0, 2 * (4 * n + 1)⟩ [fm]⊢⁺ _
          rw [show 2 * (4 * n + 1) = 8 * n + 2 from by omega]
          exact even_k0
        · -- k = 4*n+1: d = 2*(4*n+2) = 8*n+4
          obtain ⟨m', rfl⟩ : ∃ m', a = m' + (4 * n + 3) := ⟨a - (4 * n + 3), by omega⟩
          refine ⟨⟨2 * m' + 6 * n + 4, 0, 0, 2 * m' + 6 * n + 5⟩,
            ⟨2 * m' + 6 * n + 4, 2 * m' + 6 * n + 5, rfl, by omega, by omega⟩, ?_⟩
          show ⟨m' + 4 * n + 3, 0, 0, 2 * (4 * n + 2)⟩ [fm]⊢⁺ _
          rw [show 2 * (4 * n + 2) = 8 * n + 4 from by omega]
          exact even_k1
        · -- k = 4*n+2: d = 2*(4*n+3) = 8*n+6
          obtain ⟨m', rfl⟩ : ∃ m', a = m' + (4 * n + 4) := ⟨a - (4 * n + 4), by omega⟩
          refine ⟨⟨m' + 3 * n + 5, 0, 0, 2⟩,
            ⟨m' + 3 * n + 5, 2, rfl, by omega, by omega⟩, ?_⟩
          show ⟨m' + 4 * n + 4, 0, 0, 2 * (4 * n + 3)⟩ [fm]⊢⁺ _
          rw [show 2 * (4 * n + 3) = 8 * n + 6 from by omega]
          exact even_k2
        · -- k = 4*n+3: d = 2*(4*n+4) = 8*(n+1)
          obtain ⟨m', rfl⟩ : ∃ m', a = m' + (4 * n + 5) := ⟨a - (4 * n + 5), by omega⟩
          refine ⟨⟨2 * m' + 6 * n + 7, 0, 0, 2 * m' + 6 * n + 8⟩,
            ⟨2 * m' + 6 * n + 7, 2 * m' + 6 * n + 8, rfl, by omega, by omega⟩, ?_⟩
          show ⟨m' + 4 * n + 5, 0, 0, 2 * (4 * n + 4)⟩ [fm]⊢⁺ _
          rw [show 2 * (4 * n + 4) = 8 * (n + 1) from by omega]
          exact even_k3
      · -- d odd: d = 2*K + 1
        subst hK
        obtain ⟨n, rfl | rfl | rfl | rfl⟩ : ∃ n, K = 4 * n ∨ K = 4 * n + 1 ∨ K = 4 * n + 2 ∨ K = 4 * n + 3 :=
          ⟨K / 4, by omega⟩
        · -- K = 4*n: d = 2*(4*n)+1 = 8*n+1, n >= 1
          obtain ⟨m', rfl⟩ : ∃ m', a = m' + (4 * n + 1) := ⟨a - (4 * n + 1), by omega⟩
          refine ⟨⟨m' + 3 * n + 2, 0, 0, 3⟩,
            ⟨m' + 3 * n + 2, 3, rfl, by omega, by omega⟩, ?_⟩
          show ⟨m' + 4 * n + 1, 0, 0, 2 * (4 * n) + 1⟩ [fm]⊢⁺ _
          rw [show 2 * (4 * n) + 1 = 8 * n + 1 from by omega]
          exact odd_j0
        · -- K = 4*n+1: d = 2*(4*n+1)+1 = 8*n+3
          obtain ⟨m', rfl⟩ : ∃ m', a = m' + (4 * n + 3) := ⟨a - (4 * n + 3), by omega⟩
          refine ⟨⟨m' + 3 * n + 4, 0, 0, 2⟩,
            ⟨m' + 3 * n + 4, 2, rfl, by omega, by omega⟩, ?_⟩
          show ⟨m' + 4 * n + 3, 0, 0, 2 * (4 * n + 1) + 1⟩ [fm]⊢⁺ _
          rw [show 2 * (4 * n + 1) + 1 = 8 * n + 3 from by omega]
          exact odd_j1
        · -- K = 4*n+2: d = 2*(4*n+2)+1 = 8*n+5
          obtain ⟨m', rfl⟩ : ∃ m', a = m' + (4 * n + 4) := ⟨a - (4 * n + 4), by omega⟩
          refine ⟨⟨m' + 3 * n + 4, 0, 0, 2⟩,
            ⟨m' + 3 * n + 4, 2, rfl, by omega, by omega⟩, ?_⟩
          show ⟨m' + 4 * n + 4, 0, 0, 2 * (4 * n + 2) + 1⟩ [fm]⊢⁺ _
          rw [show 2 * (4 * n + 2) + 1 = 8 * n + 5 from by omega]
          exact odd_j2
        · -- K = 4*n+3: d = 2*(4*n+3)+1 = 8*n+7
          obtain ⟨m', rfl⟩ : ∃ m', a = m' + (4 * n + 5) := ⟨a - (4 * n + 5), by omega⟩
          refine ⟨⟨2 * m' + 6 * n + 8, 0, 0, 2 * m' + 6 * n + 9⟩,
            ⟨2 * m' + 6 * n + 8, 2 * m' + 6 * n + 9, rfl, by omega, by omega⟩, ?_⟩
          show ⟨m' + 4 * n + 5, 0, 0, 2 * (4 * n + 3) + 1⟩ [fm]⊢⁺ _
          rw [show 2 * (4 * n + 3) + 1 = 8 * n + 7 from by omega]
          exact odd_j3
  · exact ⟨3, 2, rfl, by omega, by omega⟩
