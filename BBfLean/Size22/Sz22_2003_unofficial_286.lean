import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #286: [14/15, 9/22, 125/2, 11/7, 6/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -1
-1  0  3  0  0
 0  0  0 -1  1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_286

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem r3_chain : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 3 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d; step fm
    rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring]
    exact ih (c + 3) d

theorem r4_chain : ∀ k c d, ⟨0, 0, c, d + k, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, k⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih c (d + 1))
    step fm; exists 0

theorem inner_loop : ∀ k a c d e,
    ⟨a + 1, 0, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨a + 1 + k, (0 : ℕ), c, d + 2 * k, e⟩ := by
  intro k; induction k with
  | zero => intro a c d e; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show a + 1 + (k + 1) = (a + 1) + 1 + k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    exact ih (a + 1) c (d + 2) e

theorem r2_drain : ∀ k a b d,
    ⟨a + 1 + k, b, 0, d, k⟩ [fm]⊢* ⟨a + 1, b + 2 * k, (0 : ℕ), d, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show a + 1 + (k + 1) = (a + 1 + k) + 1 from by ring]
    step fm
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    exact ih a (b + 2) d

theorem ab_process : ∀ B A d, A ≥ 1 →
    ⟨A, B, 0, d, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, 3 * A + 2 * B, d + B, 0⟩ := by
  intro B
  induction' B using Nat.strongRecOn with B ihB
  intro A d hA
  rcases B with _ | _ | _ | B
  · rw [show 3 * A + 2 * 0 = 0 + 3 * A from by ring, show d + 0 = d from by ring]
    exact r3_chain A 0 d
  · obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
    step fm; step fm
    rw [show 3 * (A' + 1) + 2 * 1 = 2 + 3 * (A' + 1) from by ring]
    exact r3_chain (A' + 1) 2 (d + 1)
  · obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
    step fm; step fm; step fm
    rw [show 3 * (A' + 1) + 2 * 2 = 1 + 3 * (A' + 2) from by ring]
    exact r3_chain (A' + 2) 1 (d + 2)
  · obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
    step fm; step fm; step fm; step fm
    rw [show 3 * (A' + 1) + 2 * (B + 3) = 3 * (A' + 3) + 2 * B from by ring,
        show d + (B + 3) = (d + 3) + B from by ring]
    exact ihB B (by omega) (A' + 3) (d + 3) (by omega)

-- Easy case: inner loop runs D full times
theorem main_trans_easy (c D : ℕ) :
    ⟨2, 0, c + 2 * D, 1, D⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 2 * D + D + 6, 2 * D + 1, 0⟩ := by
  have h1 := inner_loop D 1 c 1 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show 1 + 1 + D = D + 2 from by ring,
      show 1 + 2 * D = 2 * D + 1 from by ring,
      show c + 2 * D + D + 6 = c + 3 * (D + 2) from by ring]
  exact r3_chain (D + 2) c (2 * D + 1)

-- Hard case: inner loop runs K times, then R2 drain + ab_process
-- Subcase C%2 = 0
theorem main_trans_hard_even (K D : ℕ) (hDK : D ≥ K + 1) (hKD : 2 * K ≥ D) :
    ⟨K + 2, 0, 0, 2 * K + 1, D - K⟩ [fm]⊢* ⟨(0 : ℕ), 0, 2 * K + D + 6, 2 * D + 1, 0⟩ := by
  have h1 := r2_drain (D - K) (2 * K + 1 - D) 0 (2 * K + 1)
  simp only [Nat.zero_add] at h1
  rw [show (2 * K + 1 - D) + 1 + (D - K) = K + 2 from by omega] at h1
  apply stepStar_trans h1
  apply stepStar_trans (ab_process (2 * (D - K)) ((2 * K + 1 - D) + 1) (2 * K + 1) (by omega))
  suffices h : 3 * ((2 * K + 1 - D) + 1) + 2 * (2 * (D - K)) = 2 * K + D + 6 ∧
               2 * K + 1 + 2 * (D - K) = 2 * D + 1 by
    rw [h.1, h.2]; exists 0
  constructor <;> omega

-- Subcase C%2 = 1, E = 0
theorem main_trans_hard_odd_zero (K : ℕ) (D : ℕ) (hDK : D = K + 1) :
    ⟨K + 2, 0, 1, 2 * K + 1, 1⟩ [fm]⊢* ⟨(0 : ℕ), 0, 2 * K + 1 + D + 6, 2 * D + 1, 0⟩ := by
  step fm; step fm
  apply stepStar_trans (ab_process 1 (K + 2) (2 * K + 2) (by omega))
  suffices h : 3 * (K + 2) + 2 * 1 = 2 * K + 1 + D + 6 ∧
               2 * K + 2 + 1 = 2 * D + 1 by
    rw [h.1, h.2]; exists 0
  constructor <;> omega

-- Subcase C%2 = 1, E ≥ 1
theorem main_trans_hard_odd_pos (K E : ℕ) (D : ℕ) (hDK : D - K = E + 2) (hKE : K ≥ E + 1) :
    ⟨K + 2, 0, 1, 2 * K + 1, E + 2⟩ [fm]⊢* ⟨(0 : ℕ), 0, 2 * K + 1 + D + 6, 2 * D + 1, 0⟩ := by
  step fm; step fm
  -- Now at (K+2, 1, 0, 2K+2, E+1)
  have h1 := r2_drain (E + 1) (K - E) 1 (2 * K + 2)
  rw [show (K - E) + 1 + (E + 1) = K + 2 from by omega] at h1
  apply stepStar_trans h1
  apply stepStar_trans (ab_process (1 + 2 * (E + 1)) ((K - E) + 1) (2 * K + 2) (by omega))
  suffices h : 3 * ((K - E) + 1) + 2 * (1 + 2 * (E + 1)) = 2 * K + 1 + D + 6 ∧
               2 * K + 2 + (1 + 2 * (E + 1)) = 2 * D + 1 by
    rw [h.1, h.2]; exists 0
  constructor <;> omega

theorem main_trans (C D : ℕ) (h : C ≥ D) :
    ⟨0, 0, C + 2, D, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, C + D + 6, 2 * D + 1, 0⟩ := by
  -- Phase 1: R4 chain
  rw [show (D : ℕ) = 0 + D from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain D (C + 2) 0)
  -- Phase 2: R5 + R1
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm; step fm
  -- Now at (2, 0, C, 1, D). Goal: (2, 0, C, 1, D) ⊢* (0, 0, C+D+6, 2D+1, 0)
  simp only [Nat.zero_add]
  by_cases h2 : C ≥ 2 * D
  · -- Easy case: C = (C - 2D) + 2D
    show (2, 0, C, 1, D) [fm]⊢* ((0 : ℕ), 0, C + D + 6, 2 * D + 1, 0)
    have h3 := main_trans_easy (C - 2 * D) D
    simp only [show C - 2 * D + 2 * D = C from by omega] at h3
    exact h3
  · push_neg at h2
    set K := C / 2
    have hCK : C = C % 2 + 2 * K := by omega
    have hDK : D ≥ K + 1 := by omega
    -- Inner loop K times
    have hloop := inner_loop K 1 (C % 2) 1 (D - K)
    rw [show 1 + 1 + K = K + 2 from by ring,
        show 1 + 2 * K = 2 * K + 1 from by ring] at hloop
    apply stepStar_trans
    · rw [show C = C % 2 + 2 * K from hCK,
          show D = (D - K) + K from by omega]
      exact hloop
    -- Now at (K+2, 0, C%2, 2K+1, D-K)
    rcases Nat.mod_two_eq_zero_or_one C with hmod | hmod
    · -- C%2 = 0
      rw [hmod, show C + D + 6 = 2 * K + D + 6 from by omega]
      exact main_trans_hard_even K D hDK (by omega)
    · -- C%2 = 1
      rw [hmod]
      rcases (show D = K + 1 ∨ D ≥ K + 2 from by omega) with hDK1 | hDK2
      · -- D = K + 1, so D - K = 1
        rw [show D - K = 1 from by omega,
            show C + D + 6 = 2 * K + 1 + D + 6 from by omega]
        exact main_trans_hard_odd_zero K D (by omega)
      · -- D ≥ K + 2, so D - K ≥ 2
        rw [show D - K = (D - K - 2) + 2 from by omega,
            show C + D + 6 = 2 * K + 1 + D + 6 from by omega]
        exact main_trans_hard_odd_pos K (D - K - 2) D (by omega) (by omega)

theorem bootstrap : c₀ [fm]⊢* ⟨(0 : ℕ), 0, 1 + 2, 0, 0⟩ := by
  unfold c₀; execute fm 1

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts bootstrap
  apply progress_nonhalt (P := fun q ↦ ∃ C D, q = ⟨(0 : ℕ), 0, C + 2, D, 0⟩ ∧ C ≥ D)
  · intro q ⟨C, D, hq, hCD⟩
    subst hq
    refine ⟨⟨0, 0, C + D + 6, 2 * D + 1, 0⟩, ?_, main_trans C D hCD⟩
    refine ⟨C + D + 4, 2 * D + 1, ?_, by omega⟩
    show ((0 : ℕ), 0, C + D + 6, 2 * D + 1, 0) = ((0 : ℕ), 0, (C + D + 4) + 2, 2 * D + 1, 0)
    simp [show C + D + 6 = (C + D + 4) + 2 from by ring]
  · exact ⟨1, 0, rfl, by omega⟩

end Sz22_2003_unofficial_286
