import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1642: [77/15, 27/14, 22/3, 5/11, 9/2]

Vector representation:
```
 0 -1 -1  1  1
-1  3  0 -1  0
 1 -1  0  0  1
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude
-/

namespace Sz22_2003_unofficial_1642

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
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
  · simp
    rw [show A + B + 1 = A + (B + 1) from by ring,
        show E + B + 1 = E + (B + 1) from by ring]
    exact r3_chain (B + 1) A E
  · rcases A with _ | A
    · step fm
      rw [show (1 : ℕ) = 0 + 1 from rfl,
          show (D : ℕ) + 1 = D + 1 from rfl]
      step fm
      rw [show 0 + B + 2 * (D + 1) + 1 = 0 + (B + 2) + 2 * D + 1 from by ring,
          show E + B + 3 * (D + 1) + 1 = (E + 1) + (B + 2) + 3 * D + 1 from by ring,
          show B + 3 = (B + 2) + 1 from by ring]
      exact ih 0 (B + 2) (E + 1)
    · rw [show A + 1 = A + 1 from rfl,
          show (D : ℕ) + 1 = D + 1 from rfl]
      step fm
      rw [show A + 1 + B + 2 * (D + 1) + 1 = A + (B + 3) + 2 * D + 1 from by ring,
          show E + B + 3 * (D + 1) + 1 = E + (B + 3) + 3 * D + 1 from by ring,
          show B + 1 + 3 = (B + 3) + 1 from by ring]
      exact ih A (B + 3) E

theorem full_drain : ∀ C, ∀ A D E, 3 * A ≥ C →
    ⟨A, 3, C, D, E⟩ [fm]⊢* ⟨A + C + 2 * D + 3, 0, 0, 0, E + 3 * C + 3 * D + 3⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro A D E hA
  rcases C with _ | _ | _ | C
  · simp
    rw [show (3 : ℕ) = 2 + 1 from rfl,
        show A + 2 * D + 3 = A + 2 + 2 * D + 1 from by ring,
        show E + 3 * D + 3 = E + 2 + 3 * D + 1 from by ring]
    exact bd_drain D A 2 E
  · rw [show (3 : ℕ) = 2 + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show A + 1 + 2 * D + 3 = A + 1 + 2 * (D + 1) + 1 from by ring,
        show E + 3 * 1 + 3 * D + 3 = (E + 1) + 1 + 3 * (D + 1) + 1 from by ring]
    exact bd_drain (D + 1) A 1 (E + 1)
  · rw [show (3 : ℕ) = 1 + 1 + 1 from rfl,
        show (2 : ℕ) = 0 + 1 + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show A + 2 + 2 * D + 3 = A + 0 + 2 * (D + 2) + 1 from by ring,
        show E + 3 * 2 + 3 * D + 3 = (E + 2) + 0 + 3 * (D + 2) + 1 from by ring]
    exact bd_drain (D + 2) A 0 (E + 2)
  · have hA1 : A ≥ 1 := by omega
    rw [show (3 : ℕ) = 2 + 1 from rfl,
        show C + 3 = (C + 2) + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show C + 2 = (C + 1) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show C + 1 = C + 1 from rfl]
    step fm
    rw [show A = (A - 1) + 1 from by omega,
        show D + 3 = (D + 2) + 1 from by ring]
    step fm
    have goal_a : A - 1 + 1 + (C + 1 + 1 + 1) + 2 * D + 3 =
        (A - 1) + C + 2 * (D + 2) + 3 := by omega
    have goal_e : E + 3 * (C + 1 + 1 + 1) + 3 * D + 3 =
        (E + 3) + 3 * C + 3 * (D + 2) + 3 := by ring
    rw [goal_a, goal_e]
    exact ih C (by omega) (A - 1) (D + 2) (E + 3) (by omega)

theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺ ⟨3 * n + 5, 0, 6 * n + 8, 0, 0⟩ := by
  have p1 : ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢* ⟨n, 3, 2 * n, 1, 2⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]
    step fm -- R5: (n+1, 2, 2n+2, 0, 0)
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
    step fm -- R1: (n+1, 1, 2n+1, 1, 1)
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show 2 * n + 1 = (2 * n) + 1 from by ring]
    step fm -- R1: (n+1, 0, 2n, 2, 2)
    rw [show n + 1 = n + 1 from rfl,
        show (2 : ℕ) = 1 + 1 from rfl]
    step fm -- R2: (n, 3, 2n, 1, 2)
    finish
  have p2 : ⟨n, 3, 2 * n, 1, 2⟩ [fm]⊢*
      ⟨3 * n + 5, 0, 0, 0, 6 * n + 8⟩ := by
    rw [show 3 * n + 5 = n + 2 * n + 2 * 1 + 3 from by ring,
        show 6 * n + 8 = 2 + 3 * (2 * n) + 3 * 1 + 3 from by ring]
    exact full_drain (2 * n) n 1 2 (by omega)
  have p3 : ⟨3 * n + 5, 0, 0, 0, 6 * n + 8⟩ [fm]⊢*
      ⟨3 * n + 5, 0, 6 * n + 8, 0, 0⟩ := by
    have := e_to_c (a := 3 * n + 5) (6 * n + 8) 0; simpa using this
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus
      (stepStar_stepPlus p2 (by unfold Q; simp))
      p3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩)
  · unfold c₀; execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 2 * n + 2, 0, 0⟩) 0
  intro n
  refine ⟨3 * n + 3, ?_⟩
  show ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺
    ⟨(3 * n + 3) + 2, 0, 2 * (3 * n + 3) + 2, 0, 0⟩
  rw [show (3 * n + 3) + 2 = 3 * n + 5 from by ring,
      show 2 * (3 * n + 3) + 2 = 6 * n + 8 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1642
