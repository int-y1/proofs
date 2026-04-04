import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1782: [9/10, 3773/2, 2/21, 5/49, 2/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  3  1
 1 -1  0 -1  0
 0  0  1 -2  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1782

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨0, 0, c, (d + 2) + 2 * k, e⟩ [fm]⊢* ⟨0, 0, c + 1 + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · step fm; finish
  · rw [show (d + 2) + 2 * (k + 1) = ((d + 2) + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish


theorem r3_r2_chain : ∀ k, ⟨0, b + k, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + 1 + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    step fm
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih (b := b) (d := d + 2) (e := e + 1))
    ring_nf; finish

theorem r1_r5_drain : ∀ k, ⟨1, b, k, 0, k⟩ [fm]⊢* ⟨1, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

theorem phase2 : ∀ k, ⟨0, 0, k + 1, 1, k + 1⟩ [fm]⊢* ⟨1, 2 * k + 1, 0, 0, 0⟩ := by
  intro k
  step fm
  step fm
  step fm
  show ⟨1, 1, k, 0, k⟩ [fm]⊢* ⟨1, 2 * k + 1, 0, 0, 0⟩
  apply stepStar_trans (r1_r5_drain k (b := 1))
  ring_nf; finish

theorem main_trans (e : ℕ) : ⟨0, 0, 0, 2 * e + 3, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * e + 5, 2 * e + 2⟩ := by
  have h1 : ⟨0, 0, 0, 2 * e + 3, e + 1⟩ [fm]⊢* ⟨0, 0, e + 1, 1, e + 1⟩ := by
    rw [show 2 * e + 3 = (1 + 2) + 2 * e from by ring]
    apply stepStar_trans (r4_chain e (c := 0) (d := 1) (e := e + 1))
    ring_nf; finish
  have h2 : ⟨0, 0, e + 1, 1, e + 1⟩ [fm]⊢* ⟨1, 2 * e + 1, 0, 0, 0⟩ :=
    phase2 e
  have h4 : ⟨1, 2 * e + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨0, 2 * e + 1, 0, 3, 1⟩ := by
    step fm; finish
  have h5 : ⟨0, 2 * e + 1, 0, 3, 1⟩ [fm]⊢* ⟨0, 0, 0, 4 * e + 5, 2 * e + 2⟩ := by
    rw [show (3 : ℕ) = 2 + 1 from by ring,
        show 2 * e + 1 = 0 + (2 * e + 1) from by ring]
    apply stepStar_trans (r3_r2_chain (2 * e + 1) (b := 0) (d := 2) (e := 1))
    ring_nf; finish
  apply stepStar_stepPlus_stepPlus h1
  apply stepStar_stepPlus_stepPlus h2
  apply stepPlus_stepStar_stepPlus h4
  exact h5

theorem main_trans' (e : ℕ) : ⟨0, 0, 0, 2 * e + 3, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (2 * e + 1) + 3, (2 * e + 1) + 1⟩ := by
  have h := main_trans e
  rw [show 4 * e + 5 = 2 * (2 * e + 1) + 3 from by ring,
      show 2 * e + 2 = (2 * e + 1) + 1 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨0, 0, 0, 2 * e + 3, e + 1⟩) 0
  intro e; exists 2 * e + 1; exact main_trans' e
