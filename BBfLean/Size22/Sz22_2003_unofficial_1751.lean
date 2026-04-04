import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1751: [9/10, 1/42, 22/3, 7/2, 5/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
-1 -1  0 -1  0
 1 -1  0  0  1
-1  0  0  1  0
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1751

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+1, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_c : ∀ k, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem a_to_d : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem b_to_ae : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ b c D e, ⟨0, b + 1, c + k, D, e⟩ [fm]⊢* ⟨0, b + 1 + k, c, D, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c D e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) c D (e + 1))
    ring_nf; finish

theorem r3r2_drain : ∀ k, ⟨0, b + 2 * k + 1, 0, k, e⟩ [fm]⊢* ⟨0, b + 1, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show b + 2 * (k + 1) + 1 = (b + 2 * k + 1) + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b := b) (e := e + 1))
    ring_nf; finish

theorem phase_r6r3r1 :
    ⟨0, 0, C + 1, D + 1, 0⟩ [fm]⊢⁺ ⟨0, 2, C, D, 1⟩ := by
  step fm; step fm; step fm; finish

theorem main_phase (D F : ℕ) :
    ⟨0, 0, 2 * D + F + 1, D + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, F + 2, 2 * F + 3 * D + 3⟩ := by
  rw [show 2 * D + F + 1 = (2 * D + F) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus phase_r6r3r1
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  rw [show (1 + 1) * D + F = 0 + (2 * D + F) from by ring]
  apply stepStar_trans (r3r1_chain (2 * D + F) 1 0 D 1)
  rw [show 1 + 1 + (2 * D + F) = (F + 1) + 2 * D + 1 from by ring,
      show 1 + (2 * D + F) = 2 * D + F + 1 from by ring]
  apply stepStar_trans (r3r2_drain D (b := F + 1) (e := 2 * D + F + 1))
  rw [show F + 1 + 1 = 0 + (F + 2) from by ring,
      show 2 * D + F + 1 + D = 3 * D + F + 1 from by ring]
  apply stepStar_trans (b_to_ae (F + 2) (a := 0) (b := 0) (e := 3 * D + F + 1))
  rw [show 0 + (F + 2) = (F + 1) + 1 from by ring,
      show 3 * D + F + 1 + (F + 2) = (2 * F + 3 * D + 3) from by ring]
  rw [show F + 1 + 1 = 0 + (F + 2) from by ring,
      show (1 + 1) * F + 3 * D + 3 = 2 * F + 3 * D + 3 from by ring]
  exact a_to_d (F + 2) (a := 0) (d := 0) (e := 2 * F + 3 * D + 3)

theorem main_trans (D F : ℕ) :
    ⟨0, 0, 0, D + 1, 2 * D + F + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, F + 2, 2 * F + 3 * D + 3⟩ := by
  rw [show 2 * D + F + 1 = 0 + (2 * D + F + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * D + F + 1) (c := 0) (d := D + 1) (e := 0))
  rw [show 0 + (2 * D + F + 1) = 2 * D + F + 1 from by ring]
  exact main_phase D F

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 0, p.1 + 1, 2 * p.1 + p.2 + 1⟩) ⟨0, 0⟩
  intro ⟨D, F⟩
  refine ⟨⟨F + 1, 3 * D⟩, ?_⟩
  show ⟨0, 0, 0, D + 1, 2 * D + F + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, (F + 1) + 1, 2 * (F + 1) + 3 * D + 1⟩
  rw [show (F + 1) + 1 = F + 2 from by ring,
      show 2 * (F + 1) + 3 * D + 1 = 2 * F + 3 * D + 3 from by ring]
  exact main_trans D F
