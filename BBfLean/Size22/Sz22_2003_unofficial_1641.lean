import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1641: [77/15, 27/14, 22/3, 5/11, 21/2]

Vector representation:
```
 0 -1 -1  1  1
-1  3  0 -1  0
 1 -1  0  0  1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude
-/

namespace Sz22_2003_unofficial_1641

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  step fm; apply stepStar_trans (ih (c + 1)); ring_nf; finish

theorem r3_chain : ∀ k, ∀ A E, ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + k, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  step fm
  rw [show A + (k + 1) = (A + 1) + k from by ring,
      show E + (k + 1) = (E + 1) + k from by ring]
  exact ih (A + 1) (E + 1)

theorem bd_drain : ∀ D, ∀ A B E,
    ⟨A, B + 1, 0, D, E⟩ [fm]⊢* ⟨A + B + 2 * D + 1, 0, 0, 0, E + B + 3 * D + 1⟩ := by
  intro D; induction' D with D ih <;> intro A B E
  · -- D = 0: R3 chain
    simp
    rw [show A + B + 1 = A + (B + 1) from by ring,
        show E + B + 1 = E + (B + 1) from by ring]
    exact r3_chain (B + 1) A E
  · -- D+1: case split on A
    rcases A with _ | A
    · -- A = 0: R3, then R2, then IH
      step fm -- R3: (1, B, 0, D+1, E+1)
      rw [show (1 : ℕ) = 0 + 1 from rfl,
          show (D : ℕ) + 1 = D + 1 from rfl]
      step fm -- R2: (0, B+3, 0, D, E+1)
      rw [show 0 + B + 2 * (D + 1) + 1 = 0 + (B + 2) + 2 * D + 1 from by ring,
          show E + B + 3 * (D + 1) + 1 = (E + 1) + (B + 2) + 3 * D + 1 from by ring,
          show B + 3 = (B + 2) + 1 from by ring]
      exact ih 0 (B + 2) (E + 1)
    · -- A+1 ≥ 1: R2, then IH
      rw [show A + 1 = A + 1 from rfl,
          show (D : ℕ) + 1 = D + 1 from rfl]
      step fm -- R2: (A, B+4, 0, D, E)
      rw [show A + 1 + B + 2 * (D + 1) + 1 = A + (B + 3) + 2 * D + 1 from by ring,
          show E + B + 3 * (D + 1) + 1 = E + (B + 3) + 3 * D + 1 from by ring,
          show B + 1 + 3 = (B + 3) + 1 from by ring]
      exact ih A (B + 3) E

theorem full_drain : ∀ C, ∀ A D E, 3 * A ≥ C →
    ⟨A, 3, C, D, E⟩ [fm]⊢* ⟨A + C + 2 * D + 3, 0, 0, 0, E + 3 * C + 3 * D + 3⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro A D E hA
  rcases C with _ | _ | _ | C
  · -- C = 0: bd_drain with B=2
    simp
    rw [show (3 : ℕ) = 2 + 1 from rfl,
        show A + 2 * D + 3 = A + 2 + 2 * D + 1 from by ring,
        show E + 3 * D + 3 = E + 2 + 3 * D + 1 from by ring]
    exact bd_drain D A 2 E
  · -- C = 1: R1, then bd_drain
    rw [show (3 : ℕ) = 2 + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm -- R1: (A, 2, 0, D+1, E+1)
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show A + 1 + 2 * D + 3 = A + 1 + 2 * (D + 1) + 1 from by ring,
        show E + 3 * 1 + 3 * D + 3 = (E + 1) + 1 + 3 * (D + 1) + 1 from by ring]
    exact bd_drain (D + 1) A 1 (E + 1)
  · -- C = 2: R1×2, then bd_drain
    rw [show (3 : ℕ) = 1 + 1 + 1 from rfl,
        show (2 : ℕ) = 0 + 1 + 1 from rfl]
    step fm -- R1: (A, 2, 1, D+1, E+1)
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm -- R1: (A, 1, 0, D+2, E+2)
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show A + 2 + 2 * D + 3 = A + 0 + 2 * (D + 2) + 1 from by ring,
        show E + 3 * 2 + 3 * D + 3 = (E + 2) + 0 + 3 * (D + 2) + 1 from by ring]
    exact bd_drain (D + 2) A 0 (E + 2)
  · -- C ≥ 3 (actual value C+3): R1×3, R2, then IH
    have hA1 : A ≥ 1 := by omega
    rw [show (3 : ℕ) = 2 + 1 from rfl,
        show C + 3 = (C + 2) + 1 from by ring]
    step fm -- R1
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show C + 2 = (C + 1) + 1 from by ring]
    step fm -- R1
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show C + 1 = C + 1 from rfl]
    step fm -- R1: (A, 0, C, D+3, E+3)
    rw [show A = (A - 1) + 1 from by omega,
        show D + 3 = (D + 2) + 1 from by ring]
    step fm -- R2: (A-1, 3, C, D+2, E+3)
    have goal_a : A - 1 + 1 + (C + 1 + 1 + 1) + 2 * D + 3 =
        (A - 1) + C + 2 * (D + 2) + 3 := by omega
    have goal_e : E + 3 * (C + 1 + 1 + 1) + 3 * D + 3 =
        (E + 3) + 3 * C + 3 * (D + 2) + 3 := by ring
    rw [goal_a, goal_e]
    exact ih C (by omega) (A - 1) (D + 2) (E + 3) (by omega)

theorem main_trans (n : ℕ) :
    ⟨3 * n + 3, 0, 6 * n + 4, 0, 0⟩ [fm]⊢⁺ ⟨9 * n + 9, 0, 18 * n + 16, 0, 0⟩ := by
  -- R5: (3n+2, 1, 6n+4, 1, 0)
  -- R1: (3n+2, 0, 6n+3, 2, 1)
  -- R2: (3n+1, 3, 6n+3, 1, 1)
  have p1 : ⟨3 * n + 3, 0, 6 * n + 4, 0, 0⟩ [fm]⊢* ⟨3 * n + 1, 3, 6 * n + 3, 1, 1⟩ := by
    rw [show 3 * n + 3 = (3 * n + 2) + 1 from by ring]
    step fm -- R5: (3n+2, 1, 6n+4, 1, 0)
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show 6 * n + 4 = (6 * n + 3) + 1 from by ring]
    step fm -- R1: (3n+2, 0, 6n+3, 2, 1)
    rw [show 3 * n + 2 = (3 * n + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from rfl]
    step fm -- R2: (3n+1, 3, 6n+3, 1, 1)
    finish
  have p2 : ⟨3 * n + 1, 3, 6 * n + 3, 1, 1⟩ [fm]⊢*
      ⟨9 * n + 9, 0, 0, 0, 18 * n + 16⟩ := by
    rw [show 9 * n + 9 = (3 * n + 1) + (6 * n + 3) + 2 * 1 + 3 from by ring,
        show 18 * n + 16 = 1 + 3 * (6 * n + 3) + 3 * 1 + 3 from by ring]
    exact full_drain (6 * n + 3) (3 * n + 1) 1 1 (by omega)
  have p3 : ⟨9 * n + 9, 0, 0, 0, 18 * n + 16⟩ [fm]⊢*
      ⟨9 * n + 9, 0, 18 * n + 16, 0, 0⟩ := by
    have := e_to_c (a := 9 * n + 9) (18 * n + 16) 0; simpa using this
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus
      (stepStar_stepPlus p2 (by unfold Q; simp))
      p3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 4, 0, 0⟩)
  · unfold c₀; execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n + 3, 0, 6 * n + 4, 0, 0⟩) 0
  intro n
  refine ⟨3 * n + 2, ?_⟩
  show ⟨3 * n + 3, 0, 6 * n + 4, 0, 0⟩ [fm]⊢⁺
    ⟨3 * (3 * n + 2) + 3, 0, 6 * (3 * n + 2) + 4, 0, 0⟩
  rw [show 3 * (3 * n + 2) + 3 = 9 * n + 9 from by ring,
      show 6 * (3 * n + 2) + 4 = 18 * n + 16 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1641
