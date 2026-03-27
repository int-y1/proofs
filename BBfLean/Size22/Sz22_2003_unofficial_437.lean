import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #437: [27/35, 25/33, 22/5, 7/11, 55/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  2  0 -1
 1  0 -1  0  1
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_437

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- 5-step reduction: decreases d by 3, increases b by 8
theorem reduce_d3 : ⟨a+1, B, 0, d+3, 0⟩ [fm]⊢⁺ ⟨a, B+8, 0, d, 0⟩ := by
  execute fm 5

-- Repeated d reduction by induction
theorem reduce_d3_star : ⟨a+k, B, 0, d+3*k, 0⟩ [fm]⊢* ⟨a, B+8*k, 0, d, 0⟩ := by
  have h : ∀ k a B, ⟨a+k, B, 0, d+3*k, 0⟩ [fm]⊢* ⟨a, B+8*k, 0, d, 0⟩ := by
    intro k; induction' k with k ih <;> intro a B
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 3 * (k + 1) = (d + 3 * k) + 3 from by ring]
    apply stepStar_trans (stepPlus_stepStar reduce_d3)
    apply stepStar_trans (ih _ _)
    rw [show B + 8 + 8 * k = B + 8 * (k + 1) from by ring]
    exists 0
  exact h k a B

-- Rule 3 repeated: convert c to a+e when b=0, d=0
theorem c_to_ae : ⟨A, 0, C+k, 0, E⟩ [fm]⊢* ⟨A+k, 0, C, 0, E+k⟩ := by
  have h : ∀ k A E, ⟨A, 0, C+k, 0, E⟩ [fm]⊢* ⟨A+k, 0, C, 0, E+k⟩ := by
    intro k; induction' k with k ih <;> intro A E
    · exists 0
    rw [show C + (k + 1) = (C + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h k A E

-- Rule 4 repeated: convert e to d
theorem e_to_d : ⟨A, 0, 0, D, E+k⟩ [fm]⊢* ⟨A, 0, 0, D+k, E⟩ := by
  have h : ∀ k D, ⟨A, 0, 0, D, E+k⟩ [fm]⊢* ⟨A, 0, 0, D+k, E⟩ := by
    intro k; induction' k with k ih <;> intro D
    · exists 0
    rw [show E + (k + 1) = (E + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish
  exact h k D

-- Alternating rule3/rule2: (A, B+k, C+1, 0, 0) ⊢* (A+k, B, C+1+k, 0, 0)
-- Need C+1 so rule 3 can fire first
theorem bc_process : ⟨A, B+k, C+1, 0, 0⟩ [fm]⊢* ⟨A+k, B, C+1+k, 0, 0⟩ := by
  have h : ∀ k A C, ⟨A, B+k, C+1, 0, 0⟩ [fm]⊢* ⟨A+k, B, C+1+k, 0, 0⟩ := by
    intro k; induction' k with k ih <;> intro A C
    · exists 0
    rw [show B + (k + 1) = (B + k) + 1 from by ring]
    step fm; step fm
    -- now at (A+1, B+k, C+2, 0, 0); rewrite C+2 = (C+1)+1 for IH
    rw [show C + 2 = (C + 1) + 1 from by ring]
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h k A C

-- Full transition for d=0: (a+1, B+1, 0, 0, 0) ⊢⁺ (a+2*B+3, 0, 0, B+3, 0)
theorem process_b_d0 : ⟨a+1, B+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+2*B+3, 0, 0, B+3, 0⟩ := by
  -- rule 5: (a, B+1, 1, 0, 1), rule 2: (a, B, 3, 0, 0)
  step fm; step fm
  -- bc_process with C=2: (a, B, 3, 0, 0) = (a, 0+B, 2+1, 0, 0) ⊢* (a+B, 0, 3+B, 0, 0)
  rw [show (a : ℕ) = a + 0 from by ring, show (3 : ℕ) = 2 + 1 from by ring,
      show (B : ℕ) = 0 + B from by ring]
  apply stepStar_trans (bc_process (B := 0))
  rw [show a + 0 + B = a + B from by ring, show 2 + 1 + B = 0 + (B + 3) from by ring]
  -- c_to_ae: (a+B, 0, B+3, 0, 0) ⊢* (a+2B+3, 0, 0, 0, B+3)
  apply stepStar_trans (c_to_ae (C := 0) (k := B + 3))
  simp only [Nat.zero_add]
  -- e_to_d: (a+2B+3, 0, 0, 0, B+3) ⊢* (a+2B+3, 0, 0, B+3, 0)
  rw [show B + 3 = 0 + (B + 3) from by ring]
  apply stepStar_trans (e_to_d (D := 0) (k := B + 3))
  ring_nf; finish

-- Residue d=1: (a+1, B, 0, 1, 0) ⊢⁺ (a+2*B+6, 0, 0, B+4, 0)
theorem process_d1 : ⟨a+1, B, 0, 1, 0⟩ [fm]⊢⁺ ⟨a+2*B+6, 0, 0, B+4, 0⟩ := by
  -- 5 rules -> (a+1, B+1, 3, 0, 0)
  step fm; step fm; step fm; step fm; step fm
  -- bc_process: (a+1, B+1, 3, 0, 0) = (a+1, 0+(B+1), 2+1, 0, 0) ⊢* (a+B+2, 0, B+4, 0, 0)
  rw [show (a + 1 : ℕ) = a + 1 + 0 from by ring, show (3 : ℕ) = 2 + 1 from by ring,
      show B + 1 = 0 + (B + 1) from by ring]
  apply stepStar_trans (bc_process (B := 0))
  rw [show a + 1 + 0 + (B + 1) = a + B + 2 from by ring,
      show 2 + 1 + (B + 1) = 0 + (B + 4) from by ring]
  -- c_to_ae
  apply stepStar_trans (c_to_ae (C := 0) (k := B + 4))
  simp only [Nat.zero_add]
  -- e_to_d
  rw [show B + 4 = 0 + (B + 4) from by ring]
  apply stepStar_trans (e_to_d (D := 0) (k := B + 4))
  ring_nf; finish

-- Residue d=2: (a+1, B, 0, 2, 0) ⊢⁺ (a+2*B+11, 0, 0, B+6, 0)
theorem process_d2 : ⟨a+1, B, 0, 2, 0⟩ [fm]⊢⁺ ⟨a+2*B+11, 0, 0, B+6, 0⟩ := by
  -- 6 rules -> (a+1, B+4, 2, 0, 0)
  step fm; step fm; step fm; step fm; step fm; step fm
  -- bc_process: (a+1, B+4, 2, 0, 0) = (a+1, 0+(B+4), 1+1, 0, 0) ⊢* (a+B+5, 0, B+6, 0, 0)
  rw [show (a + 1 : ℕ) = a + 1 + 0 from by ring, show (2 : ℕ) = 1 + 1 from by ring,
      show B + 4 = 0 + (B + 4) from by ring]
  apply stepStar_trans (bc_process (B := 0))
  rw [show a + 1 + 0 + (B + 4) = a + B + 5 from by ring,
      show 1 + 1 + (B + 4) = 0 + (B + 6) from by ring]
  -- c_to_ae
  apply stepStar_trans (c_to_ae (C := 0) (k := B + 6))
  simp only [Nat.zero_add]
  -- e_to_d
  rw [show B + 6 = 0 + (B + 6) from by ring]
  apply stepStar_trans (e_to_d (D := 0) (k := B + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨11, 0, 0, 6, 0⟩)
  · execute fm 30
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ 3 * a ≥ d + 3)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    -- Write d = 3*k + r where r ∈ {0,1,2}
    have hmod : ∃ k r, d = 3 * k + r ∧ r < 3 := ⟨d / 3, d % 3, by omega, by omega⟩
    obtain ⟨k, r, hdk, hr⟩ := hmod
    -- Case split on r
    interval_cases r
    · -- r = 0: d = 3*k, k >= 1 since d >= 1
      subst hdk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      -- a >= k'+2 since 3a >= 3(k'+1)+3 = 3k'+6
      obtain ⟨m, rfl⟩ : ∃ m, a = m + (k' + 1) := ⟨a - (k' + 1), by omega⟩
      -- m >= 1 since 3(m+k'+1) >= 3k'+6 gives 3m >= 3
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      refine ⟨⟨m' + 2 * (8 * k' + 7) + 3, 0, 0, 8 * k' + 7 + 3, 0⟩,
        ⟨_, _, rfl, by omega, by omega⟩, ?_⟩
      rw [show 3 * (k' + 1) = 0 + 3 * (k' + 1) from by ring]
      apply stepStar_stepPlus_stepPlus (reduce_d3_star (d := 0) (k := k' + 1))
      simp only [Nat.zero_add]
      rw [show 8 * (k' + 1) = (8 * k' + 7) + 1 from by ring]
      apply stepPlus_stepStar_stepPlus (process_b_d0 (a := m') (B := 8 * k' + 7))
      ring_nf; finish
    · -- r = 1: d = 3*k + 1
      subst hdk
      -- a >= k+1 since 3a >= 3k+4
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k := ⟨a - k, by omega⟩
      -- m >= 1 since 3(m+k) >= 3k+4 gives 3m >= 4, m >= 2
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      refine ⟨⟨m' + 2 * (8 * k) + 6, 0, 0, 8 * k + 4, 0⟩,
        ⟨_, _, rfl, by omega, by omega⟩, ?_⟩
      rw [show 3 * k + 1 = 1 + 3 * k from by ring]
      apply stepStar_stepPlus_stepPlus (reduce_d3_star (d := 1) (k := k))
      simp only [Nat.zero_add]
      have h := @process_d1 m' (8 * k)
      convert h using 2
    · -- r = 2: d = 3*k + 2
      subst hdk
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k := ⟨a - k, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      refine ⟨⟨m' + 2 * (8 * k) + 11, 0, 0, 8 * k + 6, 0⟩,
        ⟨_, _, rfl, by omega, by omega⟩, ?_⟩
      rw [show 3 * k + 2 = 2 + 3 * k from by ring]
      apply stepStar_stepPlus_stepPlus (reduce_d3_star (d := 2) (k := k))
      simp only [Nat.zero_add]
      have h := @process_d2 m' (8 * k)
      convert h using 2
  · exact ⟨11, 6, rfl, by omega, by omega⟩
