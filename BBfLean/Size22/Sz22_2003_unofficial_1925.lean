import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1925: [9/70, 22/5, 25/21, 7/11, 25/2]

Vector representation:
```
-1  2 -1 -1  0
 1  0 -1  0  1
 0 -1  2 -1  0
 0  0  0  1 -1
-1  0  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1925

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

theorem triplet_chain : ∀ k A B r,
    ⟨A + 2 * k, B, 2, 3 * k + r, 0⟩ [fm]⊢* ⟨A, B + 3 * k, 2, r, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B r
  · simp; exists 0
  · rw [show A + 2 * (k + 1) = (A + 2 * k) + 1 + 1 from by ring,
        show 3 * (k + 1) + r = (3 * k + r) + 1 + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans
    · apply step_stepStar
      show (A + 2 * k, (B + 3) + 1, 0, (3 * k + r) + 1, 0) [fm]⊢
        (A + 2 * k, B + 3, 2, 3 * k + r, 0)
      simp [fm]; rfl
    rw [show B + 3 * (k + 1) = (B + 3) + 3 * k from by ring]
    apply stepStar_trans (ih A (B + 3) r)
    ring_nf; finish

theorem spiral : ∀ k A e, ⟨A, k, 0, 0, e + 1⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, 0, e + 1 + k⟩ := by
  intro k; induction' k with k ih <;> intro A e
  · simp; exists 0
  · step fm; step fm; step fm; step fm
    rw [show A + 2 * (k + 1) = (A + 2) + 2 * k from by ring,
        show e + 1 + (k + 1) = (e + 1) + 1 + k from by ring]
    apply stepStar_trans (ih (A + 2) (e + 1))
    ring_nf; finish

theorem r2r2_spiral_e2d (A B : ℕ) : ⟨A, B, 2, 0, 0⟩ [fm]⊢* ⟨A + 2 * B + 2, 0, 0, B + 2, 0⟩ := by
  step fm; step fm
  show ⟨A + 1 + 1, B, 0, 0, 1 + 1⟩ [fm]⊢* ⟨A + 2 * B + 2, 0, 0, B + 2, 0⟩
  apply stepStar_trans (spiral B (A + 1 + 1) 1)
  rw [show A + 1 + 1 + 2 * B = A + 2 * B + 2 from by ring,
      show 1 + 1 + B = B + 2 from by ring]
  apply stepStar_trans (@e_to_d (A + 2 * B + 2) (B + 2) 0)
  ring_nf; finish

theorem trans_case0 :
    ⟨A + 4 * j + 1, 0, 0, 6 * j, 0⟩ [fm]⊢⁺ ⟨A + 12 * j + 2, 0, 0, 6 * j + 2, 0⟩ := by
  rw [show A + 4 * j + 1 = (A + 4 * j) + 1 from by ring]
  step fm
  rw [show 6 * j = 3 * (2 * j) + 0 from by ring,
      show A + 4 * j = A + 2 * (2 * j) from by ring]
  apply stepStar_trans (triplet_chain (2 * j) A 0 0)
  rw [show (0 : ℕ) + 3 * (2 * j) = 6 * j from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (r2r2_spiral_e2d A (6 * j))
  ring_nf; finish

theorem case1_cleanup :
    ⟨A + 3, B, 2, 2, 0⟩ [fm]⊢* ⟨A + 2, B + 4, 0, 0, 2⟩ := by
  rw [show A + 3 = (A + 2) + 1 from by ring]
  step fm
  step fm
  rw [show A + 2 = (A + 1) + 1 from by ring]
  step fm
  step fm; step fm
  ring_nf; finish

theorem trans_case1 :
    ⟨A + 4 * j + 4, 0, 0, 6 * j + 2, 0⟩ [fm]⊢⁺ ⟨A + 12 * j + 10, 0, 0, 6 * j + 6, 0⟩ := by
  rw [show A + 4 * j + 4 = (A + 4 * j + 3) + 1 from by ring]
  step fm
  rw [show 6 * j + 2 = 3 * (2 * j) + 2 from by ring,
      show A + 4 * j + 3 = (A + 3) + 2 * (2 * j) from by ring]
  apply stepStar_trans (triplet_chain (2 * j) (A + 3) 0 2)
  rw [show (0 : ℕ) + 3 * (2 * j) = 6 * j from by ring]
  apply stepStar_trans (case1_cleanup (A := A) (B := 6 * j))
  show ⟨A + 2, 6 * j + 4, 0, 0, 1 + 1⟩ [fm]⊢* ⟨A + 12 * j + 10, 0, 0, 6 * j + 6, 0⟩
  apply stepStar_trans (spiral (6 * j + 4) (A + 2) 1)
  rw [show A + 2 + 2 * (6 * j + 4) = A + 12 * j + 10 from by ring,
      show 1 + 1 + (6 * j + 4) = 6 * j + 6 from by ring]
  apply stepStar_trans (@e_to_d (A + 12 * j + 10) (6 * j + 6) 0)
  ring_nf; finish

theorem case2_first_two_steps :
    ⟨A, B + 3, 2, 1, 0⟩ [fm]⊢* ⟨A, B + 5, 0, 0, 1⟩ := by
  rcases A with _ | A
  · step fm; step fm; finish
  · step fm; step fm; ring_nf; finish

theorem case2_cleanup :
    ⟨A, B + 3, 2, 1, 0⟩ [fm]⊢* ⟨A + 2, B + 4, 0, 0, 2⟩ := by
  apply stepStar_trans case2_first_two_steps
  step fm
  apply stepStar_trans
  · apply step_stepStar
    show (A, (B + 4) + 1, 0, (0) + 1, 0) [fm]⊢ (A, B + 4, 2, 0, 0)
    simp [fm]; rfl
  step fm; step fm
  ring_nf; finish

theorem trans_case2 :
    ⟨A + 4 * j + 3, 0, 0, 6 * j + 4, 0⟩ [fm]⊢⁺ ⟨A + 12 * j + 10, 0, 0, 6 * j + 6, 0⟩ := by
  rw [show A + 4 * j + 3 = (A + 4 * j + 2) + 1 from by ring]
  step fm
  rw [show 6 * j + 4 = 3 * (2 * j + 1) + 1 from by ring,
      show A + 4 * j + 2 = A + 2 * (2 * j + 1) from by ring]
  apply stepStar_trans (triplet_chain (2 * j + 1) A 0 1)
  rw [show (0 : ℕ) + 3 * (2 * j + 1) = 6 * j + 3 from by ring]
  apply stepStar_trans (case2_cleanup (A := A) (B := 6 * j))
  show ⟨A + 2, 6 * j + 4, 0, 0, 1 + 1⟩ [fm]⊢* ⟨A + 12 * j + 10, 0, 0, 6 * j + 6, 0⟩
  apply stepStar_trans (spiral (6 * j + 4) (A + 2) 1)
  rw [show A + 2 + 2 * (6 * j + 4) = A + 12 * j + 10 from by ring,
      show 1 + 1 + (6 * j + 4) = 6 * j + 6 from by ring]
  apply stepStar_trans (@e_to_d (A + 12 * j + 10) (6 * j + 6) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 4, 0⟩) (by execute fm 19)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a D, q = ⟨a, 0, 0, D, 0⟩ ∧ a ≥ D + 1 ∧ D ≥ 4 ∧ ∃ m, D = 2 * m)
  · intro c ⟨a, D, hq, ha, hD, m, hm⟩; subst hq; subst hm
    obtain ⟨n, rfl | rfl | rfl⟩ : ∃ n, m = 3 * n ∨ m = 3 * n + 1 ∨ m = 3 * n + 2 :=
      ⟨m / 3, by omega⟩
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      obtain ⟨A, rfl⟩ : ∃ A, a = A + 4 * (j + 1) + 1 := ⟨a - 4 * (j + 1) - 1, by omega⟩
      refine ⟨_, ⟨A + 12 * (j + 1) + 2, 6 * (j + 1) + 2, rfl, by omega, by omega,
        3 * (j + 1) + 1, by ring⟩, ?_⟩
      show ⟨A + 4 * (j + 1) + 1, 0, 0, 2 * (3 * (j + 1)), 0⟩ [fm]⊢⁺ _
      rw [show 2 * (3 * (j + 1)) = 6 * (j + 1) from by ring]
      exact trans_case0
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      obtain ⟨A, rfl⟩ : ∃ A, a = A + 4 * (j + 1) + 4 :=
        ⟨a - 4 * (j + 1) - 4, by omega⟩
      refine ⟨_, ⟨A + 12 * (j + 1) + 10, 6 * (j + 1) + 6, rfl, by omega, by omega,
        3 * (j + 1) + 3, by ring⟩, ?_⟩
      show ⟨A + 4 * (j + 1) + 4, 0, 0, 2 * (3 * (j + 1) + 1), 0⟩ [fm]⊢⁺ _
      rw [show 2 * (3 * (j + 1) + 1) = 6 * (j + 1) + 2 from by ring]
      exact trans_case1
    · obtain ⟨A, rfl⟩ : ∃ A, a = A + 4 * n + 3 := ⟨a - 4 * n - 3, by omega⟩
      refine ⟨_, ⟨A + 12 * n + 10, 6 * n + 6, rfl, by omega, by omega,
        3 * n + 3, by ring⟩, ?_⟩
      show ⟨A + 4 * n + 3, 0, 0, 2 * (3 * n + 2), 0⟩ [fm]⊢⁺ _
      rw [show 2 * (3 * n + 2) = 6 * n + 4 from by ring]
      exact trans_case2
  · exact ⟨5, 4, rfl, by omega, by omega, 2, by ring⟩
