import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1753: [9/10, 2/21, 3773/2, 5/11, 33/7]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  0
-1  0  0  3  1
 0  0  1  0 -1
 0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1753

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ K, ∀ B D, ⟨0, B + 1, K + 1, D + K + 1, 1⟩ [fm]⊢* ⟨0, B + K + 2, 0, D, 1⟩ := by
  intro K; induction' K with K ih <;> intro B D
  · step fm; step fm; finish
  · step fm; step fm
    show ⟨0, B + 2, K + 1, D + K + 1, 1⟩ [fm]⊢* ⟨0, B + K + 3, 0, D, 1⟩
    apply stepStar_trans (ih (B := B + 1) (D := D))
    ring_nf; finish

theorem spiral : ∀ K, ∀ D, ⟨0, 0, K + 1, D + K + 2, 0⟩ [fm]⊢* ⟨0, K + 2, 0, D, 1⟩ := by
  intro K D
  step fm
  show ⟨0, 1, K + 1, D + K + 1, 1⟩ [fm]⊢* ⟨0, K + 2, 0, D, 1⟩
  apply stepStar_trans (r2r1_chain K 0 D)
  ring_nf; finish

theorem r2_chain : ∀ k, ⟨a, b + k, 0, d + k, e⟩ [fm]⊢* ⟨a + k, b, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 3))
    ring_nf; finish

theorem main_trans : ∀ k, ⟨0, 0, 0, k * k + 9 * k + 23, 2 * k + 9⟩ [fm]⊢⁺
    ⟨0, 0, 0, k * k + 11 * k + 33, 2 * k + 11⟩ := by
  intro k
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans (e_to_c (2 * k + 9) (c := 0) (d := k * k + 9 * k + 23))
    apply stepStar_trans
    · show ⟨0, 0, 0 + (2 * k + 9), k * k + 9 * k + 23, 0⟩ [fm]⊢*
        ⟨0, (2 * k + 8) + 2, 0, k * k + 7 * k + 13, 1⟩
      rw [show (0 : ℕ) + (2 * k + 9) = (2 * k + 8) + 1 from by ring,
          show k * k + 9 * k + 23 = (k * k + 7 * k + 13) + (2 * k + 8) + 2 from by ring]
      exact spiral (2 * k + 8) (k * k + 7 * k + 13)
    rw [show (2 * k + 8) + 2 = 0 + ((2 * k + 8) + 2) from by ring,
        show k * k + 7 * k + 13 = (k * k + 5 * k + 3) + ((2 * k + 8) + 2) from by ring]
    exact r2_chain ((2 * k + 8) + 2) (a := 0) (b := 0) (d := k * k + 5 * k + 3) (e := 1)
  apply step_stepStar_stepPlus
  · show ⟨0 + ((2 * k + 8) + 2), 0, 0, k * k + 5 * k + 3, 1⟩ [fm]⊢
      ⟨0 + ((2 * k + 8) + 2) - 1, 0, 0, k * k + 5 * k + 3 + 3, 1 + 1⟩
    rfl
  rw [show 0 + ((2 * k + 8) + 2) - 1 = 0 + ((2 * k + 8) + 1) from by omega,
      show k * k + 5 * k + 3 + 3 = k * k + 5 * k + 6 from by ring,
      show (1 : ℕ) + 1 = 2 from by ring,
      show k * k + 11 * k + 33 = k * k + 5 * k + 6 + 3 * ((2 * k + 8) + 1) from by ring,
      show 2 * k + 11 = 2 + ((2 * k + 8) + 1) from by ring]
  exact r3_chain ((2 * k + 8) + 1) (a := 0) (d := k * k + 5 * k + 6) (e := 2)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 23, 9⟩) (by execute fm 93)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 0, k * k + 9 * k + 23, 2 * k + 9⟩) 0
  intro k
  refine ⟨k + 1, ?_⟩
  rw [show (k + 1) * (k + 1) + 9 * (k + 1) + 23 = k * k + 11 * k + 33 from by ring,
      show 2 * (k + 1) + 9 = 2 * k + 11 from by ring]
  exact main_trans k
