import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1674: [77/15, 9/14, 2/3, 5/11, 2541/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 1 -1  0  0  0
 0  0  1  0 -1
-1  1  0  1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1674

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+2⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, (0 : ℕ), 0⟩ := by
  intro k; induction k with
  | zero => intro A C; simp; exists 0
  | succ k ih =>
    intro A C; step fm
    rw [show C + (k + 1) = (C + 1) + k from by ring]
    exact ih A (C + 1)

theorem b_to_a : ∀ k, ∀ A E,
    ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + k, 0, 0, (0 : ℕ), E⟩ := by
  intro k; induction k with
  | zero => intro A E; simp; exists 0
  | succ k ih =>
    intro A E; step fm
    apply stepStar_trans (ih (A + 1) E); ring_nf; finish

theorem r1r1r2_round : ∀ A C D E,
    ⟨A + 1, 2, C + 2, D, E⟩ [fm]⊢* ⟨A, 2, C, D + 1, E + 2⟩ := by
  intro A C D E
  rw [show (2 : ℕ) = 1 + 1 from by ring, show C + 2 = (C + 1) + 1 from by ring]
  step fm
  rw [show (C + 1 : ℕ) = C + 1 from rfl]
  step fm
  rw [show (A + 1 : ℕ) = A + 1 from rfl, show D + 2 = (D + 1) + 1 from by ring]
  step fm; ring_nf; finish

theorem interleaved_drain : ∀ A, ∀ D E,
    ⟨A, 2, 2 * A + 1, D, E⟩ [fm]⊢* ⟨0, 1, 0, D + A + 1, E + 2 * A + 1⟩ := by
  intro A; induction A with
  | zero =>
    intro D E
    rw [show 2 * 0 + 1 = (0 : ℕ) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show D + 0 + 1 = D + 1 from by ring,
        show E + 2 * 0 + 1 = E + 1 from by ring]; finish
  | succ A ih =>
    intro D E
    rw [show 2 * (A + 1) + 1 = (2 * A + 1) + 2 from by ring,
        show (A + 1 : ℕ) = A + 1 from rfl]
    apply stepStar_trans (r1r1r2_round A (2 * A + 1) D E)
    apply stepStar_trans (ih (D + 1) (E + 2))
    rw [show D + 1 + A + 1 = D + (A + 1) + 1 from by ring,
        show E + 2 + 2 * A + 1 = E + 2 * (A + 1) + 1 from by ring]; finish

theorem r3r2_step : ∀ B E,
    ⟨0, B + 1, 0, (1 : ℕ), E⟩ [fm]⊢* ⟨0, B + 2, 0, (0 : ℕ), E⟩ := by
  intro B E; step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; ring_nf; finish

theorem r3r2_gen : ∀ B D E,
    ⟨0, B + 1, 0, D + 1, E⟩ [fm]⊢* ⟨0, B + 2, 0, D, E⟩ := by
  intro B D E; step fm
  rw [show (D + 1 : ℕ) = D + 1 from rfl]
  step fm; ring_nf; finish

theorem r3r2_chain : ∀ k, ∀ B E,
    ⟨0, B + 1, 0, k, E⟩ [fm]⊢* ⟨0, B + 1 + k, 0, (0 : ℕ), E⟩ := by
  intro k; induction k with
  | zero => intro B E; simp; exists 0
  | succ k ih =>
    intro B E
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    apply stepStar_trans (r3r2_gen B k E)
    apply stepStar_trans (ih (B + 1) E); ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, 0, 2 * n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, (0 : ℕ), 2 * (n + 1)⟩ := by
  rcases n with _ | n
  · execute fm 5
  · have p1 : ⟨n + 2, 0, 0, 0, 2 * (n + 1)⟩ [fm]⊢* ⟨n + 2, 0, 2 * (n + 1), (0 : ℕ), 0⟩ := by
      have h := e_to_c (2 * (n + 1)) (n + 2) 0
      rw [show 0 + 2 * (n + 1) = 2 * (n + 1) from by ring] at h; exact h
    have p2 : ⟨n + 2, 0, 2 * (n + 1), 0, 0⟩ [fm]⊢⁺ ⟨n + 1, 1, 2 * (n + 1), 1, 2⟩ := by
      rw [show n + 2 = (n + 1) + 1 from by ring]
      step fm; finish
    have p3 : ⟨n + 1, 1, 2 * (n + 1), 1, 2⟩ [fm]⊢* ⟨n + 1, 0, 2 * n + 1, 2, 3⟩ := by
      rw [show (1 : ℕ) = 0 + 1 from by ring,
          show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
      step fm; ring_nf; finish
    have p4 : ⟨n + 1, 0, 2 * n + 1, 2, 3⟩ [fm]⊢* ⟨n, 2, 2 * n + 1, 1, 3⟩ := by
      rw [show n + 1 = n + 1 from rfl, show (2 : ℕ) = 1 + 1 from by ring]
      step fm; ring_nf; finish
    have p5 : ⟨n, 2, 2 * n + 1, 1, 3⟩ [fm]⊢* ⟨0, 1, 0, n + 2, 2 * n + 4⟩ := by
      have h := interleaved_drain n 1 3
      rw [show 1 + n + 1 = n + 2 from by ring,
          show 3 + 2 * n + 1 = 2 * n + 4 from by ring] at h; exact h
    have p6 : ⟨0, 1, 0, n + 2, 2 * n + 4⟩ [fm]⊢* ⟨0, n + 3, 0, (0 : ℕ), 2 * n + 4⟩ := by
      rw [show (1 : ℕ) = 0 + 1 from by ring]
      have h := r3r2_chain (n + 2) 0 (2 * n + 4)
      rw [show 0 + 1 + (n + 2) = n + 3 from by ring] at h; exact h
    have p7 : ⟨0, n + 3, 0, 0, 2 * n + 4⟩ [fm]⊢* ⟨n + 3, 0, 0, (0 : ℕ), 2 * n + 4⟩ := by
      have h := b_to_a (n + 3) 0 (2 * n + 4)
      rw [show 0 + (n + 3) = n + 3 from by ring] at h; exact h
    have goal_rw : (n + 3 : ℕ) = (n + 1) + 2 := by ring
    have goal_rw2 : (2 * n + 4 : ℕ) = 2 * ((n + 1) + 1) := by ring
    rw [goal_rw, goal_rw2] at p7
    exact stepStar_stepPlus_stepPlus p1
      (stepPlus_stepStar_stepPlus p2
        (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 (stepStar_trans p6 p7)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, 2 * n⟩) 0
  intro n; exists n + 1
  exact main_trans n

end Sz22_2003_unofficial_1674
