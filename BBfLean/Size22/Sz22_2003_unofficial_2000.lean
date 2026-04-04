import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #2000: [99/35, 5/66, 7/3, 4/7, 15/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  1  0 -1
 0 -1  0  1  0
 2  0  0 -1  0
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_2000

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r5r2_chain : ∀ k, ⟨2 * k + 2, 0, c, 0, k⟩ [fm]⊢* ⟨(2 : ℕ), 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 from by ring]
    step fm; step fm
    rw [show c + 1 + 1 = c + 2 from by ring]
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

theorem r3r1_chain : ∀ c, ⟨(0 : ℕ), b + 1, c + 1, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), b + c + 2, 0, 0, e + c + 1⟩ := by
  intro c; induction' c with c ih generalizing b e
  · step fm; step fm; finish
  · step fm; step fm
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

theorem b_to_d : ∀ k, ⟨(0 : ℕ), k, 0, d, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem d_to_a : ∀ k, ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

theorem six_steps : ⟨(2 : ℕ), 0, c + 1, 0, 0⟩ [fm]⊢* ⟨(0 : ℕ), 2, c + 1, 0, 1⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem all_phases : ⟨2 * n + 4, 0, 0, 0, n + 1⟩ [fm]⊢* ⟨4 * n + 8, 0, 0, 0, 2 * n + 3⟩ := by
  rw [show 2 * n + 4 = 2 * (n + 1) + 2 from by ring]
  apply stepStar_trans (r5r2_chain (n + 1) (c := 0))
  rw [show (0 : ℕ) + 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  apply stepStar_trans (six_steps (c := 2 * n + 1))
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r1_chain (2 * n + 1) (b := 1) (e := 1))
  rw [show 1 + (2 * n + 1) + 2 = 2 * n + 4 from by ring,
      show 1 + (2 * n + 1) + 1 = 2 * n + 3 from by ring]
  apply stepStar_trans (b_to_d (2 * n + 4) (d := 0) (e := 2 * n + 3))
  rw [show (0 : ℕ) + (2 * n + 4) = 2 * n + 4 from by ring]
  apply stepStar_trans (d_to_a (2 * n + 4) (a := 0) (e := 2 * n + 3))
  rw [show (0 : ℕ) + 2 * (2 * n + 4) = 4 * n + 8 from by ring]
  finish

theorem main_trans : ⟨2 * n + 4, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨4 * n + 8, 0, 0, 0, 2 * n + 3⟩ :=
  stepStar_stepPlus all_phases (by simp [Q]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 1⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 4, 0, 0, 0, n + 1⟩) 0
  intro n; exists 2 * n + 2
  show ⟨2 * n + 4, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨2 * (2 * n + 2) + 4, 0, 0, 0, 2 * n + 2 + 1⟩
  rw [show 2 * (2 * n + 2) + 4 = 4 * n + 8 from by ring,
      show 2 * n + 2 + 1 = 2 * n + 3 from by ring]
  exact main_trans

end Sz22_2003_unofficial_2000
