import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1681: [77/15, 9/14, 22/3, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 1 -1  0  0  1
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1681

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ K, ∀ A C E,
    ⟨A, 0, C, 0, E + 2 * K⟩ [fm]⊢* ⟨A, 0, C + K, (0 : ℕ), E⟩ := by
  intro K; induction' K with K ih <;> intro A C E
  · simp; exists 0
  · rw [show E + 2 * (K + 1) = E + 2 * K + 2 from by ring]
    step fm
    rw [show C + (K + 1) = (C + 1) + K from by ring]
    exact ih A (C + 1) E

theorem r3_chain : ∀ K, ∀ A E,
    ⟨A, K, 0, 0, E⟩ [fm]⊢* ⟨A + K, 0, 0, (0 : ℕ), E + K⟩ := by
  intro K; induction' K with K ih <;> intro A E
  · simp; exists 0
  · rw [show (K + 1 : ℕ) = K + 1 from rfl]
    step fm
    rw [show A + (K + 1) = (A + 1) + K from by ring,
        show E + (K + 1) = (E + 1) + K from by ring]
    exact ih (A + 1) (E + 1)

theorem r2r1r1_chain : ∀ K, ∀ A C D E,
    ⟨A + K, 0, C + 2 * K, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + K + 1, E + 2 * K⟩ := by
  intro K; induction' K with K ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (K + 1) = (A + K) + 1 from by ring,
        show C + 2 * (K + 1) = (C + 2 * K + 1) + 1 from by ring]
    step fm
    rw [show (C + 2 * K + 1 : ℕ) = (C + 2 * K) + 1 from by ring]
    step fm; step fm
    rw [show D + (K + 1) + 1 = (D + 1) + K + 1 from by ring,
        show E + 2 * (K + 1) = (E + 2) + 2 * K from by ring]
    exact ih A C (D + 1) (E + 2)

theorem r2_bulk : ∀ K, ∀ B D E,
    ⟨K, B, 0, D + K, E⟩ [fm]⊢* ⟨0, B + 2 * K, 0, D, E⟩ := by
  intro K; induction' K with K ih <;> intro B D E
  · simp; exists 0
  · rw [show D + (K + 1) = D + K + 1 from by ring,
        show (K + 1 : ℕ) = K + 1 from rfl]
    step fm
    rw [show B + 2 * (K + 1) = (B + 2) + 2 * K from by ring]
    exact ih (B + 2) D E

-- K pairs of (R3, R2) starting from (0, B+1, 0, D+K+1, E)
-- After each (R3, R2) pair: b increases by 1, d decreases by 1, e increases by 1
-- After K pairs: (0, B+K+1, 0, D+1, E+K)
theorem r3r2_pairs : ∀ K, ∀ B D E,
    ⟨0, B + 1, 0, D + K + 1, E⟩ [fm]⊢* ⟨0, B + K + 1, 0, D + 1, E + K⟩ := by
  intro K; induction' K with K ih <;> intro B D E
  · simp; exists 0
  · rw [show D + (K + 1) + 1 = D + K + 1 + 1 from by ring,
        show (B + 1 : ℕ) = B + 1 from rfl]
    step fm
    rw [show D + K + 1 + 1 = (D + K + 1) + 1 from by ring,
        show (B : ℕ) = B from rfl]
    step fm
    rw [show B + (K + 1) + 1 = (B + 1) + K + 1 from by ring,
        show E + (K + 1) = (E + 1) + K from by ring,
        show D + 1 = D + 1 from rfl]
    exact ih (B + 1) D (E + 1)

-- C=0 drain: (A+1, 0, 0, D+A+2, E) ⊢* (1, 2*A+D+1, 0, 1, E+D+1)
-- r2_bulk (A+1): (0, 2A+2, 0, D+1, E)
-- r3r2_pairs D: (0, 2A+D+2, 0, 1, E+D)
-- R3: (1, 2A+D+1, 0, 1, E+D+1)
theorem c0_drain (A D E : ℕ) :
    ⟨A + 1, 0, 0, D + A + 2, E⟩ [fm]⊢* ⟨1, 2 * A + D + 1, 0, 1, E + D + 1⟩ := by
  have p1 : ⟨A + 1, 0, 0, D + A + 2, E⟩ [fm]⊢* ⟨0, 2 * A + 2, 0, D + 1, E⟩ := by
    have h := r2_bulk (A + 1) 0 (D + 1) E
    rw [show 0 + 2 * (A + 1) = 2 * A + 2 from by ring,
        show D + 1 + (A + 1) = D + A + 2 from by ring] at h
    exact h
  have p2 : ⟨0, 2 * A + 2, 0, D + 1, E⟩ [fm]⊢* ⟨0, 2 * A + D + 2, 0, 1, E + D⟩ := by
    have h := r3r2_pairs D (2 * A + 1) 0 E
    rw [show 2 * A + 1 + 1 = 2 * A + 2 from by ring,
        show 0 + D + 1 = D + 1 from by ring,
        show 2 * A + 1 + D + 1 = 2 * A + D + 2 from by ring,
        show 0 + 1 = 1 from rfl] at h
    exact h
  have p3 : ⟨0, 2 * A + D + 2, 0, 1, E + D⟩ [fm]⊢* ⟨1, 2 * A + D + 1, 0, 1, E + D + 1⟩ := by
    rw [show (2 * A + D + 2 : ℕ) = (2 * A + D + 1) + 1 from by ring]
    step fm; ring_nf; finish
  exact stepStar_trans p1 (stepStar_trans p2 p3)

-- C=1 drain: (A+1, 0, 1, D+A+1, E) ⊢* (1, 2*A+D, 0, 1, E+D+2)
-- R2+R1: (A, 1, 0, D+A+1, E+1)
-- r2_bulk A: (0, 2A+1, 0, D+1, E+1)
-- r3r2_pairs D: (0, 2A+D+1, 0, 1, E+D+1)
-- R3: (1, 2A+D, 0, 1, E+D+2)
theorem c1_drain (A D E : ℕ) :
    ⟨A + 1, 0, 1, D + A + 1, E⟩ [fm]⊢* ⟨1, 2 * A + D, 0, 1, E + D + 2⟩ := by
  have p1 : ⟨A + 1, 0, 1, D + A + 1, E⟩ [fm]⊢* ⟨A, 1, 0, D + A + 1, E + 1⟩ := by
    rw [show (A + 1 : ℕ) = A + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl,
        show D + A + 1 = (D + A) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  have p2 : ⟨A, 1, 0, D + A + 1, E + 1⟩ [fm]⊢* ⟨0, 2 * A + 1, 0, D + 1, E + 1⟩ := by
    have h := r2_bulk A 1 (D + 1) (E + 1)
    rw [show 1 + 2 * A = 2 * A + 1 from by ring,
        show D + 1 + A = D + A + 1 from by ring] at h
    exact h
  have p3 : ⟨0, 2 * A + 1, 0, D + 1, E + 1⟩ [fm]⊢* ⟨0, 2 * A + D + 1, 0, 1, E + D + 1⟩ := by
    have h := r3r2_pairs D (2 * A) 0 (E + 1)
    rw [show 2 * A + 1 = 2 * A + 1 from rfl,
        show 0 + D + 1 = D + 1 from by ring,
        show 2 * A + D + 1 = 2 * A + D + 1 from rfl,
        show 0 + 1 = 1 from rfl,
        show E + 1 + D = E + D + 1 from by ring] at h
    exact h
  have p4 : ⟨0, 2 * A + D + 1, 0, 1, E + D + 1⟩ [fm]⊢* ⟨1, 2 * A + D, 0, 1, E + D + 2⟩ := by
    rw [show (2 * A + D + 1 : ℕ) = (2 * A + D) + 1 from by ring]
    step fm; ring_nf; finish
  exact stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3 p4))

theorem final_phase (B E : ℕ) :
    ⟨1, B, 0, 1, E⟩ [fm]⊢⁺ ⟨B + 2, 0, 0, (0 : ℕ), E + B + 2⟩ := by
  have p1 : ⟨1, B, 0, 1, E⟩ [fm]⊢⁺ ⟨0, B + 2, 0, 0, E⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  have p2 : ⟨0, B + 2, 0, 0, E⟩ [fm]⊢* ⟨B + 2, 0, 0, (0 : ℕ), E + (B + 2)⟩ := by
    have h := r3_chain (B + 2) 0 E
    rw [show 0 + (B + 2) = B + 2 from by ring] at h; exact h
  rw [show E + B + 2 = E + (B + 2) from by ring]
  exact stepPlus_stepStar_stepPlus p1 p2

-- n ≡ 1 mod 4: transition from (4m+2, 0, 0, 0, 12m+3) to (4m+3, 0, 0, 0, 12m+6)
-- Phases: R4(6m+1) -> R5+R1 -> R2R1R1(3m) -> C=0 drain -> final
theorem main_trans_4m1 (m : ℕ) :
    ⟨4 * m + 2, 0, 0, 0, 12 * m + 3⟩ [fm]⊢⁺ ⟨4 * m + 3, 0, 0, (0 : ℕ), 12 * m + 6⟩ := by
  have p_r4 : ⟨4 * m + 2, 0, 0, 0, 12 * m + 3⟩ [fm]⊢*
      ⟨4 * m + 2, 0, 6 * m + 1, 0, 1⟩ := by
    rw [show (12 * m + 3 : ℕ) = 1 + 2 * (6 * m + 1) from by ring]
    have h := r4_chain (6 * m + 1) (4 * m + 2) 0 1
    rw [show 0 + (6 * m + 1) = 6 * m + 1 from by ring] at h; exact h
  have p_open : ⟨4 * m + 2, 0, 6 * m + 1, 0, 1⟩ [fm]⊢*
      ⟨4 * m + 1, 0, 6 * m, 2, 2⟩ := by
    rw [show 4 * m + 2 = (4 * m + 1) + 1 from by ring,
        show (6 * m + 1 : ℕ) = 6 * m + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show (6 * m + 1 : ℕ) = (6 * m) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- R2R1R1(3m): (4m+1, 0, 6m, 2, 2) -> (m+1, 0, 0, 3m+2, 6m+2)
  have p_chain : ⟨4 * m + 1, 0, 6 * m, 2, 2⟩ [fm]⊢*
      ⟨m + 1, 0, 0, 3 * m + 2, 6 * m + 2⟩ := by
    have h := r2r1r1_chain (3 * m) (m + 1) 0 1 2
    rw [show m + 1 + 3 * m = 4 * m + 1 from by ring,
        show 0 + 2 * (3 * m) = 6 * m from by ring,
        show 1 + 1 = 2 from rfl,
        show 1 + 3 * m + 1 = 3 * m + 2 from by ring,
        show 2 + 2 * (3 * m) = 6 * m + 2 from by ring] at h; exact h
  -- C=0 drain: (m+1, 0, 0, 3m+2, 6m+2) -> (1, 4m+1, 0, 1, 8m+3)
  -- A=m, D=2m, E=6m+2. D+A+2=3m+2. 2A+D+1=4m+1. E+D+1=8m+3.
  have p_drain : ⟨m + 1, 0, 0, 3 * m + 2, 6 * m + 2⟩ [fm]⊢*
      ⟨1, 4 * m + 1, 0, 1, 8 * m + 3⟩ := by
    have h := c0_drain m (2 * m) (6 * m + 2)
    rw [show 2 * m + m + 2 = 3 * m + 2 from by ring,
        show 2 * m + 2 * m + 1 = 4 * m + 1 from by ring,
        show 6 * m + 2 + 2 * m + 1 = 8 * m + 3 from by ring] at h; exact h
  -- final: (1, 4m+1, 0, 1, 8m+3) ⊢⁺ (4m+3, 0, 0, 0, 12m+6)
  have p_final : ⟨1, 4 * m + 1, 0, 1, 8 * m + 3⟩ [fm]⊢⁺
      ⟨4 * m + 3, 0, 0, (0 : ℕ), 12 * m + 6⟩ := by
    have h := final_phase (4 * m + 1) (8 * m + 3)
    rw [show 4 * m + 1 + 2 = 4 * m + 3 from by ring,
        show 8 * m + 3 + (4 * m + 1) + 2 = 12 * m + 6 from by ring] at h; exact h
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans p_r4 (stepStar_trans p_open (stepStar_trans p_chain p_drain))) p_final

-- n ≡ 2 mod 4: transition from (4m+3, 0, 0, 0, 12m+6) to (4m+4, 0, 0, 0, 12m+9)
theorem main_trans_4m2 (m : ℕ) :
    ⟨4 * m + 3, 0, 0, 0, 12 * m + 6⟩ [fm]⊢⁺ ⟨4 * m + 4, 0, 0, (0 : ℕ), 12 * m + 9⟩ := by
  have p_r4 : ⟨4 * m + 3, 0, 0, 0, 12 * m + 6⟩ [fm]⊢*
      ⟨4 * m + 3, 0, 6 * m + 3, 0, 0⟩ := by
    rw [show (12 * m + 6 : ℕ) = 0 + 2 * (6 * m + 3) from by ring]
    have h := r4_chain (6 * m + 3) (4 * m + 3) 0 0
    rw [show 0 + (6 * m + 3) = 6 * m + 3 from by ring] at h; exact h
  have p_open : ⟨4 * m + 3, 0, 6 * m + 3, 0, 0⟩ [fm]⊢*
      ⟨4 * m + 2, 0, 6 * m + 2, 2, 1⟩ := by
    rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring,
        show (6 * m + 3 : ℕ) = (6 * m + 2) + 1 from by ring]
    step fm
    rw [show (6 * m + 2 + 1 : ℕ) = (6 * m + 2) + 1 from by ring,
        show (0 : ℕ) = 0 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- R2R1R1(3m+1): (4m+2, 0, 6m+2, 2, 1) -> (m+1, 0, 0, 3m+3, 6m+3)
  have p_chain : ⟨4 * m + 2, 0, 6 * m + 2, 2, 1⟩ [fm]⊢*
      ⟨m + 1, 0, 0, 3 * m + 3, 6 * m + 3⟩ := by
    have h := r2r1r1_chain (3 * m + 1) (m + 1) 0 1 1
    rw [show m + 1 + (3 * m + 1) = 4 * m + 2 from by ring,
        show 0 + 2 * (3 * m + 1) = 6 * m + 2 from by ring,
        show 1 + 1 = 2 from rfl,
        show 1 + (3 * m + 1) + 1 = 3 * m + 3 from by ring,
        show 1 + 2 * (3 * m + 1) = 6 * m + 3 from by ring] at h; exact h
  -- C=0 drain: (m+1, 0, 0, 3m+3, 6m+3) -> (1, 4m+2, 0, 1, 8m+5)
  -- A=m, D=2m+1, E=6m+3. D+A+2=3m+3. 2A+D+1=4m+2. E+D+1=8m+5.
  have p_drain : ⟨m + 1, 0, 0, 3 * m + 3, 6 * m + 3⟩ [fm]⊢*
      ⟨1, 4 * m + 2, 0, 1, 8 * m + 5⟩ := by
    have h := c0_drain m (2 * m + 1) (6 * m + 3)
    rw [show 2 * m + 1 + m + 2 = 3 * m + 3 from by ring,
        show 2 * m + (2 * m + 1) + 1 = 4 * m + 2 from by ring,
        show 6 * m + 3 + (2 * m + 1) + 1 = 8 * m + 5 from by ring] at h; exact h
  have p_final : ⟨1, 4 * m + 2, 0, 1, 8 * m + 5⟩ [fm]⊢⁺
      ⟨4 * m + 4, 0, 0, (0 : ℕ), 12 * m + 9⟩ := by
    have h := final_phase (4 * m + 2) (8 * m + 5)
    rw [show 4 * m + 2 + 2 = 4 * m + 4 from by ring,
        show 8 * m + 5 + (4 * m + 2) + 2 = 12 * m + 9 from by ring] at h; exact h
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans p_r4 (stepStar_trans p_open (stepStar_trans p_chain p_drain))) p_final

-- n ≡ 3 mod 4: transition from (4m+4, 0, 0, 0, 12m+9) to (4m+5, 0, 0, 0, 12m+12)
theorem main_trans_4m3 (m : ℕ) :
    ⟨4 * m + 4, 0, 0, 0, 12 * m + 9⟩ [fm]⊢⁺ ⟨4 * m + 5, 0, 0, (0 : ℕ), 12 * m + 12⟩ := by
  have p_r4 : ⟨4 * m + 4, 0, 0, 0, 12 * m + 9⟩ [fm]⊢*
      ⟨4 * m + 4, 0, 6 * m + 4, 0, 1⟩ := by
    rw [show (12 * m + 9 : ℕ) = 1 + 2 * (6 * m + 4) from by ring]
    have h := r4_chain (6 * m + 4) (4 * m + 4) 0 1
    rw [show 0 + (6 * m + 4) = 6 * m + 4 from by ring] at h; exact h
  have p_open : ⟨4 * m + 4, 0, 6 * m + 4, 0, 1⟩ [fm]⊢*
      ⟨4 * m + 3, 0, 6 * m + 3, 2, 2⟩ := by
    rw [show 4 * m + 4 = (4 * m + 3) + 1 from by ring,
        show (6 * m + 4 : ℕ) = (6 * m + 3) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show (6 * m + 3 + 1 : ℕ) = (6 * m + 3) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- R2R1R1(3m+1): (4m+3, 0, 6m+3, 2, 2) -> (m+2, 0, 1, 3m+3, 6m+4)
  have p_chain : ⟨4 * m + 3, 0, 6 * m + 3, 2, 2⟩ [fm]⊢*
      ⟨m + 2, 0, 1, 3 * m + 3, 6 * m + 4⟩ := by
    have h := r2r1r1_chain (3 * m + 1) (m + 2) 1 1 2
    rw [show m + 2 + (3 * m + 1) = 4 * m + 3 from by ring,
        show 1 + 2 * (3 * m + 1) = 6 * m + 3 from by ring,
        show 1 + 1 = 2 from rfl,
        show 1 + (3 * m + 1) + 1 = 3 * m + 3 from by ring,
        show 2 + 2 * (3 * m + 1) = 6 * m + 4 from by ring] at h; exact h
  -- C=1 drain: (m+2, 0, 1, 3m+3, 6m+4) -> (1, 4m+3, 0, 1, 8m+7)
  -- A=m+1, D=2m+1, E=6m+4. D+A+1=3m+3. 2A+D=4m+3. E+D+2=8m+7.
  have p_drain : ⟨m + 2, 0, 1, 3 * m + 3, 6 * m + 4⟩ [fm]⊢*
      ⟨1, 4 * m + 3, 0, 1, 8 * m + 7⟩ := by
    have h := c1_drain (m + 1) (2 * m + 1) (6 * m + 4)
    rw [show 2 * m + 1 + (m + 1) + 1 = 3 * m + 3 from by ring,
        show 2 * (m + 1) + (2 * m + 1) = 4 * m + 3 from by ring,
        show 6 * m + 4 + (2 * m + 1) + 2 = 8 * m + 7 from by ring] at h; exact h
  have p_final : ⟨1, 4 * m + 3, 0, 1, 8 * m + 7⟩ [fm]⊢⁺
      ⟨4 * m + 5, 0, 0, (0 : ℕ), 12 * m + 12⟩ := by
    have h := final_phase (4 * m + 3) (8 * m + 7)
    rw [show 4 * m + 3 + 2 = 4 * m + 5 from by ring,
        show 8 * m + 7 + (4 * m + 3) + 2 = 12 * m + 12 from by ring] at h; exact h
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans p_r4 (stepStar_trans p_open (stepStar_trans p_chain p_drain))) p_final

-- n ≡ 0 mod 4 (n >= 4): transition from (4m+5, 0, 0, 0, 12m+12) to (4m+6, 0, 0, 0, 12m+15)
-- (this handles n=4(m+1))
theorem main_trans_4m0 (m : ℕ) :
    ⟨4 * m + 5, 0, 0, 0, 12 * m + 12⟩ [fm]⊢⁺ ⟨4 * m + 6, 0, 0, (0 : ℕ), 12 * m + 15⟩ := by
  have p_r4 : ⟨4 * m + 5, 0, 0, 0, 12 * m + 12⟩ [fm]⊢*
      ⟨4 * m + 5, 0, 6 * m + 6, 0, 0⟩ := by
    rw [show (12 * m + 12 : ℕ) = 0 + 2 * (6 * m + 6) from by ring]
    have h := r4_chain (6 * m + 6) (4 * m + 5) 0 0
    rw [show 0 + (6 * m + 6) = 6 * m + 6 from by ring] at h; exact h
  have p_open : ⟨4 * m + 5, 0, 6 * m + 6, 0, 0⟩ [fm]⊢*
      ⟨4 * m + 4, 0, 6 * m + 5, 2, 1⟩ := by
    rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring,
        show (6 * m + 6 : ℕ) = (6 * m + 5) + 1 from by ring]
    step fm
    rw [show (6 * m + 5 + 1 : ℕ) = (6 * m + 5) + 1 from by ring,
        show (0 : ℕ) = 0 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- R2R1R1(3m+2): (4m+4, 0, 6m+5, 2, 1) -> (m+2, 0, 1, 3m+4, 6m+5)
  have p_chain : ⟨4 * m + 4, 0, 6 * m + 5, 2, 1⟩ [fm]⊢*
      ⟨m + 2, 0, 1, 3 * m + 4, 6 * m + 5⟩ := by
    have h := r2r1r1_chain (3 * m + 2) (m + 2) 1 1 1
    rw [show m + 2 + (3 * m + 2) = 4 * m + 4 from by ring,
        show 1 + 2 * (3 * m + 2) = 6 * m + 5 from by ring,
        show 1 + 1 = 2 from rfl,
        show 1 + (3 * m + 2) + 1 = 3 * m + 4 from by ring] at h; exact h
  -- C=1 drain: (m+2, 0, 1, 3m+4, 6m+5) -> (1, 4m+4, 0, 1, 8m+9)
  -- A=m+1, D=2m+2, E=6m+5. D+A+1=3m+4. 2A+D=4m+4. E+D+2=8m+9.
  have p_drain : ⟨m + 2, 0, 1, 3 * m + 4, 6 * m + 5⟩ [fm]⊢*
      ⟨1, 4 * m + 4, 0, 1, 8 * m + 9⟩ := by
    have h := c1_drain (m + 1) (2 * m + 2) (6 * m + 5)
    rw [show 2 * m + 2 + (m + 1) + 1 = 3 * m + 4 from by ring,
        show 2 * (m + 1) + (2 * m + 2) = 4 * m + 4 from by ring,
        show 6 * m + 5 + (2 * m + 2) + 2 = 8 * m + 9 from by ring] at h; exact h
  have p_final : ⟨1, 4 * m + 4, 0, 1, 8 * m + 9⟩ [fm]⊢⁺
      ⟨4 * m + 6, 0, 0, (0 : ℕ), 12 * m + 15⟩ := by
    have h := final_phase (4 * m + 4) (8 * m + 9)
    rw [show 4 * m + 4 + 2 = 4 * m + 6 from by ring,
        show 8 * m + 9 + (4 * m + 4) + 2 = 12 * m + 15 from by ring] at h; exact h
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans p_r4 (stepStar_trans p_open (stepStar_trans p_chain p_drain))) p_final

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, 3 * n + 3⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, (0 : ℕ), 3 * n + 6⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- n = 4j
      subst hk; subst hj
      rw [show j + j + (j + j) + 2 = 4 * j + 2 from by ring,
          show 3 * (j + j + (j + j)) + 3 = 12 * j + 3 from by ring,
          show j + j + (j + j) + 3 = 4 * j + 3 from by ring,
          show 3 * (j + j + (j + j)) + 6 = 12 * j + 6 from by ring]
      exact main_trans_4m1 j
    · -- n = 4j+2
      subst hk; subst hj
      rw [show 2 * j + 1 + (2 * j + 1) + 2 = 4 * j + 4 from by ring,
          show 3 * (2 * j + 1 + (2 * j + 1)) + 3 = 12 * j + 9 from by ring,
          show 2 * j + 1 + (2 * j + 1) + 3 = 4 * j + 5 from by ring,
          show 3 * (2 * j + 1 + (2 * j + 1)) + 6 = 12 * j + 12 from by ring]
      exact main_trans_4m3 j
  · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- n = 4j+1
      subst hk; subst hj
      rw [show 2 * (j + j) + 1 + 2 = 4 * j + 3 from by ring,
          show 3 * (2 * (j + j) + 1) + 3 = 12 * j + 6 from by ring,
          show 2 * (j + j) + 1 + 3 = 4 * j + 4 from by ring,
          show 3 * (2 * (j + j) + 1) + 6 = 12 * j + 9 from by ring]
      exact main_trans_4m2 j
    · -- n = 4j+3
      subst hk; subst hj
      rw [show 2 * (2 * j + 1) + 1 + 2 = 4 * j + 5 from by ring,
          show 3 * (2 * (2 * j + 1) + 1) + 3 = 12 * j + 12 from by ring,
          show 2 * (2 * j + 1) + 1 + 3 = 4 * j + 6 from by ring,
          show 3 * (2 * (2 * j + 1) + 1) + 6 = 12 * j + 15 from by ring]
      exact main_trans_4m0 j

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 3 * n + 3⟩) 0
  intro n
  exact ⟨n + 1, by
    rw [show n + 1 + 2 = n + 3 from by ring,
        show 3 * (n + 1) + 3 = 3 * n + 6 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_1681
