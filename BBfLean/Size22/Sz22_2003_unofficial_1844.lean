import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1844: [9/35, 1/30, 55/3, 2/5, 7/11, 3/2]

Vector representation:
```
 0  2 -1 -1  0
-1 -1 -1  0  0
 0 -1  1  0  1
 1  0 -1  0  0
 0  0  0  1 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1844

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r1r3_chain : ∀ k, ⟨X, n, 1, k + 1, Y⟩ [fm]⊢* ⟨X, n + k + 1, 1, 0, Y + k + 1⟩ := by
  intro k; induction' k with k ih generalizing n Y
  · step fm; step fm; ring_nf; finish
  · rw [show (k + 1) + 1 = k + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (n := n + 1) (Y := Y + 1))
    ring_nf; finish

theorem r2r3_drain : ∀ A, ∀ B F, ⟨A + 1, B + 2 * A + 1, 1, 0, F⟩ [fm]⊢* ⟨0, B, 0, 0, F + A⟩ := by
  intro A; induction' A with A ih <;> intro B F
  · step fm; ring_nf; finish
  · rw [show B + 2 * (A + 1) + 1 = (B + 2 * A + 2) + 1 from by ring,
        show A + 1 + 1 = (A + 1) + 1 from by ring]
    step fm
    rw [show (B + 2 * A + 1) + 1 = B + 2 * A + 2 from by ring]
    step fm
    apply stepStar_trans (ih B (F + 1))
    ring_nf; finish

theorem b_drain : ∀ k, ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 1) (e := e + 1))
    ring_nf; finish

theorem c_to_a : ∀ k, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

theorem main_trans_pos (A : ℕ) :
    ⟨A + 2, 0, 0, 0, E + 2 * A + 3⟩ [fm]⊢⁺ ⟨E + 2, 0, 0, 0, 2 * E + 3 * A + 6⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_d (E + 2 * A + 3) (a := A + 2) (d := 0))
  rw [show 0 + (E + 2 * A + 3) = E + 2 * A + 3 from by ring]
  step fm
  step fm
  rw [show E + 2 * A + 3 = (E + 2 * A + 2) + 1 from by ring]
  apply stepStar_trans (r1r3_chain (E + 2 * A + 2) (X := A + 1) (n := 0) (Y := 1))
  rw [show 0 + (E + 2 * A + 2) + 1 = E + 2 * A + 3 from by ring,
      show 1 + (E + 2 * A + 2) + 1 = E + 2 * A + 4 from by ring]
  rw [show E + 2 * A + 3 = E + 2 + 2 * A + 1 from by ring]
  apply stepStar_trans (r2r3_drain A (E + 2) (E + 2 * A + 4))
  rw [show E + 2 * A + 4 + A = E + 3 * A + 4 from by ring]
  apply stepStar_trans (b_drain (E + 2) (c := 0) (e := E + 3 * A + 4))
  rw [show 0 + (E + 2) = E + 2 from by ring,
      show E + 3 * A + 4 + (E + 2) = 2 * E + 3 * A + 6 from by ring]
  apply stepStar_trans (c_to_a (E + 2) (a := 0) (e := 2 * E + 3 * A + 6))
  ring_nf; finish

theorem main_trans_zero :
    ⟨1, 0, 0, 0, E + 1⟩ [fm]⊢⁺ ⟨E + 2, 0, 0, 0, 2 * E + 3⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_d (E + 1) (a := 1) (d := 0))
  rw [show 0 + (E + 1) = E + 1 from by ring]
  step fm
  step fm
  rcases E with _ | E
  · step fm; step fm
    apply stepStar_trans (b_drain 1 (c := 1) (e := 2))
    rw [show 1 + 1 = 2 from by ring, show 2 + 1 = 3 from by ring]
    apply stepStar_trans (c_to_a 2 (a := 0) (e := 3))
    ring_nf; finish
  · rw [show (E + 1) + 1 = (E + 1) + 1 from by ring]
    apply stepStar_trans (r1r3_chain (E + 1) (X := 0) (n := 0) (Y := 1))
    rw [show 0 + (E + 1) + 1 = E + 2 from by ring,
        show 1 + (E + 1) + 1 = E + 3 from by ring]
    apply stepStar_trans (b_drain (E + 2) (c := 1) (e := E + 3))
    rw [show 1 + (E + 2) = E + 3 from by ring,
        show E + 3 + (E + 2) = 2 * E + 5 from by ring]
    apply stepStar_trans (c_to_a (E + 3) (a := 0) (e := 2 * E + 5))
    ring_nf; finish

theorem main_trans :
    ⟨A + 1, 0, 0, 0, E + 2 * A + 1⟩ [fm]⊢⁺ ⟨E + 2, 0, 0, 0, 2 * E + 3 * A + 3⟩ := by
  rcases A with _ | A
  · simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    exact main_trans_zero
  · rw [show (A + 1) + 1 = A + 2 from by ring,
        show E + 2 * (A + 1) + 1 = E + 2 * A + 3 from by ring,
        show 2 * E + 3 * (A + 1) + 3 = 2 * E + 3 * A + 6 from by ring]
    exact main_trans_pos A

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, E⟩ ↦ ⟨A + 1, 0, 0, 0, E + 2 * A + 1⟩) ⟨0, 0⟩
  intro ⟨A, E⟩
  refine ⟨⟨E + 1, 3 * A⟩, ?_⟩
  show ⟨A + 1, 0, 0, 0, E + 2 * A + 1⟩ [fm]⊢⁺ ⟨(E + 1) + 1, 0, 0, 0, 3 * A + 2 * (E + 1) + 1⟩
  rw [show (E + 1) + 1 = E + 2 from by ring,
      show 3 * A + 2 * (E + 1) + 1 = 2 * E + 3 * A + 3 from by ring]
  exact main_trans
