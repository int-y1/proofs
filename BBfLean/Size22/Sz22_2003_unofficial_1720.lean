import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1720: [77/45, 6/5, 25/14, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  1
 1  1 -1  0  0
-1  0  2 -1  0
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1720

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A B, ⟨A, B, 0, 0, k⟩ [fm]⊢* ⟨A, B + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B
  · exists 0
  step fm; apply stepStar_trans (ih A (B + 1))
  rw [show B + 1 + k = B + (k + 1) from by ring]; finish

theorem r3r1r1_chain : ∀ k, ∀ A B D E,
    ⟨A + k, B + 4 * k, 0, D + 1, E⟩ [fm]⊢* ⟨A, B, 0, D + k + 1, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A B D E
  · simp; exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show B + 4 * (k + 1) = (B + 4 * k) + 4 from by ring]
  apply stepStar_trans
    (stepStar_trans (step_stepStar (show fm ⟨(A+k)+1, (B+4*k)+4, 0, D+1, E⟩ = some ⟨A+k, (B+4*k)+4, 2, D, E⟩ from by simp [fm]))
    (stepStar_trans (step_stepStar (show fm ⟨A+k, (B+4*k)+4, 2, D, E⟩ = some ⟨A+k, (B+4*k)+2, 1, D+1, E+1⟩ from by simp [fm]))
      (step_stepStar (show fm ⟨A+k, (B+4*k)+2, 1, D+1, E+1⟩ = some ⟨A+k, B+4*k, 0, D+2, E+2⟩ from by simp [fm]))))
  rw [show D + 2 = (D + 1) + 1 from by ring]
  apply stepStar_trans (ih A B (D + 1) (E + 2))
  rw [show D + 1 + k + 1 = D + (k + 1) + 1 from by ring,
      show E + 2 + 2 * k = E + 2 * (k + 1) from by ring]; finish

theorem b_step_1 : ∀ A D E,
    ⟨A + 1, 1, 0, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + 1, E + 1⟩ := by
  intro A D E
  apply stepStar_trans (step_stepStar (show fm ⟨A+1, 1, 0, D+1, E⟩ = some ⟨A, 1, 2, D, E⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar (show fm ⟨A, 1, 2, D, E⟩ = some ⟨A+1, 2, 1, D, E⟩ from by simp [fm]))
  apply step_stepStar (show fm ⟨A+1, 2, 1, D, E⟩ = some ⟨A+1, 0, 0, D+1, E+1⟩ from by simp [fm])

theorem b_step_2 : ∀ A D E,
    ⟨A + 1, 2, 0, D + 1, E⟩ [fm]⊢* ⟨A + 1, 1, 0, D + 1, E + 1⟩ := by
  intro A D E
  apply stepStar_trans (step_stepStar (show fm ⟨A+1, 2, 0, D+1, E⟩ = some ⟨A, 2, 2, D, E⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar (show fm ⟨A, 2, 2, D, E⟩ = some ⟨A, 0, 1, D+1, E+1⟩ from by simp [fm]))
  apply step_stepStar (show fm ⟨A, 0, 1, D+1, E+1⟩ = some ⟨A+1, 1, 0, D+1, E+1⟩ from by simp [fm])

theorem b_step_3 : ∀ A D E,
    ⟨A + 1, 3, 0, D + 1, E⟩ [fm]⊢* ⟨A + 1, 2, 0, D + 1, E + 1⟩ := by
  intro A D E
  apply stepStar_trans (step_stepStar (show fm ⟨A+1, 3, 0, D+1, E⟩ = some ⟨A, 3, 2, D, E⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar (show fm ⟨A, 3, 2, D, E⟩ = some ⟨A, 1, 1, D+1, E+1⟩ from by simp [fm]))
  apply step_stepStar (show fm ⟨A, 1, 1, D+1, E+1⟩ = some ⟨A+1, 2, 0, D+1, E+1⟩ from by simp [fm])

theorem b0_step : ∀ A D E,
    ⟨A + 1, 0, 0, D + 1, E⟩ [fm]⊢* ⟨A + 2, 2, 0, D, E⟩ := by
  intro A D E
  apply stepStar_trans (step_stepStar (show fm ⟨A+1, 0, 0, D+1, E⟩ = some ⟨A, 0, 2, D, E⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar (show fm ⟨A, 0, 2, D, E⟩ = some ⟨A+1, 1, 1, D, E⟩ from by simp [fm]))
  apply step_stepStar (show fm ⟨A+1, 1, 1, D, E⟩ = some ⟨A+2, 2, 0, D, E⟩ from by simp [fm])

theorem b2_drain : ∀ A D E,
    ⟨A + 1, 2, 0, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + 1, E + 2⟩ := by
  intro A D E
  apply stepStar_trans (b_step_2 A D E)
  apply b_step_1 A D (E + 1)

theorem b3_drain : ∀ A D E,
    ⟨A + 1, 3, 0, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + 1, E + 3⟩ := by
  intro A D E
  apply stepStar_trans (b_step_3 A D E)
  apply stepStar_trans (b_step_2 A D (E + 1))
  rw [show E + 1 + 1 = E + 2 from by ring]
  apply b_step_1 A D (E + 2)

theorem d_chain : ∀ D, ∀ A E,
    ⟨A + 1, 0, 0, D + 1, E⟩ [fm]⊢* ⟨A + D + 2, 2, 0, 0, E + 2 * D⟩ := by
  intro D; induction' D with D ih <;> intro A E
  · simp; exact b0_step A 0 E
  rw [show D + 1 + 1 = (D + 1) + 1 from by ring]
  apply stepStar_trans (b0_step A (D + 1) E)
  rw [show A + 2 = (A + 1) + 1 from by ring]
  apply stepStar_trans (b2_drain (A + 1) D E)
  rw [show (A + 1) + 1 = (A + 1) + 1 from rfl]
  apply stepStar_trans (ih (A + 1) (E + 2))
  rw [show A + 1 + D + 2 = A + (D + 1) + 2 from by ring,
      show E + 2 + 2 * D = E + 2 * (D + 1) from by ring]; finish

-- Helper: compose all phases for a specific parameter set
-- From (A, B, 0, D+1, E) with B ∈ {0,1,2,3} to (A+D+1, 2, 0, 0, E+B+2*D)
-- then r4_chain to final state

-- The main transition composes:
-- R5: (n+2, 3(n+1), 0, 0, 0) -> (n+1, 3(n+1), 1, 1, 0)
-- R1: -> (n+1, 3n+1, 0, 2, 1)
-- r3r1r1_chain + b_drain + d_chain + r4_chain
-- Split on n mod 4

theorem main_trans_case0 (p : ℕ) :
    ⟨4*p+1, 12*p+1, 0, 2, 1⟩ [fm]⊢* ⟨4*p+3, 12*p+6, 0, 0, 0⟩ := by
  rw [show 4*p+1 = (p+1) + 3*p from by ring,
      show 12*p+1 = 1 + 4*(3*p) from by ring]
  apply stepStar_trans (r3r1r1_chain (3*p) (p+1) 1 1 1)
  rw [show 1 + 3*p + 1 = 3*p+2 from by ring,
      show 1 + 2*(3*p) = 6*p+1 from by ring]
  apply stepStar_trans (b_step_1 p (3*p+1) (6*p+1))
  rw [show 3*p+1+1 = 3*p+2 from by ring, show 6*p+1+1 = 6*p+2 from by ring]
  apply stepStar_trans (d_chain (3*p+1) p (6*p+2))
  rw [show p+(3*p+1)+2 = 4*p+3 from by ring, show 6*p+2+2*(3*p+1) = 12*p+4 from by ring]
  apply stepStar_trans (r4_chain (12*p+4) (4*p+3) 2)
  rw [show 2+(12*p+4) = 12*p+6 from by ring]; finish

theorem main_trans_case1 (p : ℕ) :
    ⟨4*p+2, 12*p+4, 0, 2, 1⟩ [fm]⊢* ⟨4*p+4, 12*p+9, 0, 0, 0⟩ := by
  rw [show 4*p+2 = (p+1) + (3*p+1) from by ring,
      show 12*p+4 = 0 + 4*(3*p+1) from by ring]
  apply stepStar_trans (r3r1r1_chain (3*p+1) (p+1) 0 1 1)
  rw [show 1+(3*p+1)+1 = 3*p+3 from by ring, show 1+2*(3*p+1) = 6*p+3 from by ring]
  apply stepStar_trans (d_chain (3*p+2) p (6*p+3))
  rw [show p+(3*p+2)+2 = 4*p+4 from by ring, show 6*p+3+2*(3*p+2) = 12*p+7 from by ring]
  apply stepStar_trans (r4_chain (12*p+7) (4*p+4) 2)
  rw [show 2+(12*p+7) = 12*p+9 from by ring]; finish

theorem main_trans_case2 (p : ℕ) :
    ⟨4*p+3, 12*p+7, 0, 2, 1⟩ [fm]⊢* ⟨4*p+5, 12*p+12, 0, 0, 0⟩ := by
  rw [show 4*p+3 = (p+2) + (3*p+1) from by ring,
      show 12*p+7 = 3 + 4*(3*p+1) from by ring]
  apply stepStar_trans (r3r1r1_chain (3*p+1) (p+2) 3 1 1)
  rw [show 1+(3*p+1)+1 = 3*p+3 from by ring, show 1+2*(3*p+1) = 6*p+3 from by ring]
  apply stepStar_trans (b3_drain (p+1) (3*p+2) (6*p+3))
  rw [show p+1+1 = p+2 from by ring, show 3*p+2+1 = 3*p+3 from by ring,
      show 6*p+3+3 = 6*p+6 from by ring]
  apply stepStar_trans (d_chain (3*p+2) (p+1) (6*p+6))
  rw [show p+1+(3*p+2)+2 = 4*p+5 from by ring, show 6*p+6+2*(3*p+2) = 12*p+10 from by ring]
  apply stepStar_trans (r4_chain (12*p+10) (4*p+5) 2)
  rw [show 2+(12*p+10) = 12*p+12 from by ring]; finish

theorem main_trans_case3 (p : ℕ) :
    ⟨4*p+4, 12*p+10, 0, 2, 1⟩ [fm]⊢* ⟨4*p+6, 12*p+15, 0, 0, 0⟩ := by
  rw [show 4*p+4 = (p+2) + (3*p+2) from by ring,
      show 12*p+10 = 2 + 4*(3*p+2) from by ring]
  apply stepStar_trans (r3r1r1_chain (3*p+2) (p+2) 2 1 1)
  rw [show 1+(3*p+2)+1 = 3*p+4 from by ring, show 1+2*(3*p+2) = 6*p+5 from by ring]
  apply stepStar_trans (b2_drain (p+1) (3*p+3) (6*p+5))
  rw [show p+1+1 = p+2 from by ring, show 3*p+3+1 = 3*p+4 from by ring,
      show 6*p+5+2 = 6*p+7 from by ring]
  apply stepStar_trans (d_chain (3*p+3) (p+1) (6*p+7))
  rw [show p+1+(3*p+3)+2 = 4*p+6 from by ring, show 6*p+7+2*(3*p+3) = 12*p+13 from by ring]
  apply stepStar_trans (r4_chain (12*p+13) (4*p+6) 2)
  rw [show 2+(12*p+13) = 12*p+15 from by ring]; finish

theorem main_trans (n : ℕ) :
    ⟨n + 2, 3 * (n + 1), 0, 0, 0⟩ [fm]⊢⁺ ⟨n + 3, 3 * (n + 2), 0, 0, 0⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show 3 * (n + 1) = (3 * n + 1) + 2 from by ring]
  apply step_stepStar_stepPlus
    (show fm ⟨(n+1)+1, (3*n+1)+2, 0, 0, 0⟩ = some ⟨n+1, (3*n+1)+2, 1, 1, 0⟩ from by simp [fm])
  apply stepStar_trans
    (step_stepStar (show fm ⟨n+1, (3*n+1)+2, 1, 1, 0⟩ = some ⟨n+1, 3*n+1, 0, 2, 1⟩ from by simp [fm]))
  -- Now at (n+1, 3n+1, 0, 2, 1), target is (n+3, 3*(n+2), 0, 0, 0)
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
    · -- n = 4p
      have hn : n = 4 * p := by omega
      subst hn
      rw [show 3 * (4 * p) + 1 = 12*p+1 from by ring,
          show 4*p+3 = 4*p+3 from rfl,
          show 3 * (4*p + 1 + 1) = 12*p+6 from by ring]
      exact main_trans_case0 p
    · -- n = 4p+2
      have hn : n = 4 * p + 2 := by omega
      subst hn
      rw [show 4*p+2+1 = 4*p+3 from by ring,
          show 3*(4*p+2)+1 = 12*p+7 from by ring,
          show 4*p+2+3 = 4*p+5 from by ring,
          show 3*(4*p+2+1+1) = 12*p+12 from by ring]
      exact main_trans_case2 p
  · rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
    · -- n = 4p+1
      have hn : n = 4 * p + 1 := by omega
      subst hn
      rw [show 4*p+1+1 = 4*p+2 from by ring,
          show 3*(4*p+1)+1 = 12*p+4 from by ring,
          show 4*p+1+3 = 4*p+4 from by ring,
          show 3*(4*p+1+1+1) = 12*p+9 from by ring]
      exact main_trans_case1 p
    · -- n = 4p+3
      have hn : n = 4 * p + 3 := by omega
      subst hn
      rw [show 4*p+3+1 = 4*p+4 from by ring,
          show 3*(4*p+3)+1 = 12*p+10 from by ring,
          show 4*p+3+3 = 4*p+6 from by ring,
          show 3*(4*p+3+1+1) = 12*p+15 from by ring]
      exact main_trans_case3 p

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 3, 0, 0, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 3 * (n + 1), 0, 0, 0⟩) 0
  intro n; exists n + 1
  show ⟨n + 2, 3 * (n + 1), 0, 0, 0⟩ [fm]⊢⁺ ⟨(n + 1) + 2, 3 * ((n + 1) + 1), 0, 0, 0⟩
  rw [show (n + 1) + 2 = n + 3 from by ring, show 3 * ((n + 1) + 1) = 3 * (n + 2) from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1720
