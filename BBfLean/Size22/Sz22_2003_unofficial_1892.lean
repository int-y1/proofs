import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1892: [9/35, 5/363, 98/3, 11/7, 15/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -2
 1 -1  0  2  0
 0  0  0 -1  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1892

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r5_r2_chain : ∀ k, ⟨a + 1 + k, 0, c, 0, r + 2 * k⟩ [fm]⊢* ⟨a + 1, 0, c + 2 * k, 0, r⟩ := by
  intro k; induction' k with k ih generalizing a c r
  · exists 0
  · rw [show a + 1 + (k + 1) = (a + 1 + k) + 1 from by ring,
        show r + 2 * (k + 1) = (r + 2 * k) + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 2) (r := r))
    ring_nf; finish

theorem r1r1r3_chain_r0 : ∀ k, ⟨a, b, 2 * k + 1, 2, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k, 1, 2, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (b := b + 3))
    ring_nf; finish

theorem r1r1r3_chain_r1 : ∀ k, ⟨a, b, 2 * k + 1, 2, 1⟩ [fm]⊢* ⟨a + k, b + 3 * k, 1, 2, 1⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (b := b + 3))
    ring_nf; finish

theorem end_chain_r0 : ⟨a, b, 1, 2, 0⟩ [fm]⊢⁺ ⟨a + 1, b + 1, 0, 3, 0⟩ := by
  step fm; step fm; finish

theorem end_chain_r1 : ⟨a, b, 1, 2, 1⟩ [fm]⊢⁺ ⟨a + 1, b + 1, 0, 3, 1⟩ := by
  step fm; step fm; finish

theorem r3_drain_r0 : ∀ k, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (d := d + 2))
    ring_nf; finish

theorem r3_drain_r1 : ∀ k, ⟨a, k, 0, d, 1⟩ [fm]⊢* ⟨a + k, 0, 0, d + 2 * k, 1⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (d := d + 2))
    ring_nf; finish

theorem d_to_e : ∀ k, ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a) (e := e + 1))
    ring_nf; finish

theorem r5_r3_r0 : ⟨a + 1, 0, c, 0, 0⟩ [fm]⊢⁺ ⟨a + 1, 0, c + 1, 2, 0⟩ := by
  step fm; step fm; finish

theorem r5_r3_r1 : ⟨a + 1, 0, c, 0, 1⟩ [fm]⊢⁺ ⟨a + 1, 0, c + 1, 2, 1⟩ := by
  step fm; step fm; finish

theorem even_trans : ⟨k + 1 + F, 0, 0, 0, 2 * k⟩ [fm]⊢⁺ ⟨4 * k + 3 + F, 0, 0, 0, 6 * k + 5⟩ := by
  rw [show k + 1 + F = F + 1 + k from by ring,
      show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_stepPlus_stepPlus (r5_r2_chain k (a := F) (c := 0) (r := 0))
  rw [show 0 + 2 * k = 2 * k from by ring]
  apply stepPlus_stepStar_stepPlus (r5_r3_r0 (a := F) (c := 2 * k))
  rw [show 2 * k + 1 = 2 * k + 1 from rfl]
  apply stepStar_trans (r1r1r3_chain_r0 k (a := F + 1) (b := 0))
  rw [show 0 + 3 * k = 3 * k from by ring]
  apply stepStar_trans (stepPlus_stepStar (end_chain_r0 (a := F + 1 + k) (b := 3 * k)))
  rw [show F + 1 + k + 1 = F + k + 2 from by ring,
      show 3 * k + 1 = 3 * k + 1 from rfl]
  apply stepStar_trans (r3_drain_r0 (3 * k + 1) (a := F + k + 2) (d := 3))
  rw [show F + k + 2 + (3 * k + 1) = F + 4 * k + 3 from by ring,
      show 3 + 2 * (3 * k + 1) = 6 * k + 5 from by ring]
  apply stepStar_trans (d_to_e (6 * k + 5) (a := F + 4 * k + 3) (e := 0))
  ring_nf; finish

theorem odd_trans : ⟨4 * k + 3 + F, 0, 0, 0, 6 * k + 5⟩ [fm]⊢⁺ ⟨13 * k + 11 + F, 0, 0, 0, 18 * k + 18⟩ := by
  rw [show 4 * k + 3 + F = (k + F) + 1 + (3 * k + 2) from by ring,
      show 6 * k + 5 = 1 + 2 * (3 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r5_r2_chain (3 * k + 2) (a := k + F) (c := 0) (r := 1))
  rw [show 0 + 2 * (3 * k + 2) = 6 * k + 4 from by ring]
  apply stepPlus_stepStar_stepPlus (r5_r3_r1 (a := k + F) (c := 6 * k + 4))
  rw [show 6 * k + 4 + 1 = 2 * (3 * k + 2) + 1 from by ring]
  apply stepStar_trans (r1r1r3_chain_r1 (3 * k + 2) (a := k + F + 1) (b := 0))
  rw [show 0 + 3 * (3 * k + 2) = 9 * k + 6 from by ring,
      show k + F + 1 + (3 * k + 2) = 4 * k + F + 3 from by ring]
  apply stepStar_trans (stepPlus_stepStar (end_chain_r1 (a := 4 * k + F + 3) (b := 9 * k + 6)))
  rw [show 4 * k + F + 3 + 1 = 4 * k + F + 4 from by ring,
      show 9 * k + 6 + 1 = 9 * k + 7 from by ring]
  apply stepStar_trans (r3_drain_r1 (9 * k + 7) (a := 4 * k + F + 4) (d := 3))
  rw [show 4 * k + F + 4 + (9 * k + 7) = 13 * k + F + 11 from by ring,
      show 3 + 2 * (9 * k + 7) = 18 * k + 17 from by ring]
  apply stepStar_trans (d_to_e (18 * k + 17) (a := 13 * k + F + 11) (e := 1))
  rw [show 1 + (18 * k + 17) = 18 * k + 18 from by ring]
  ring_nf; finish

theorem main_trans : ⟨k + 1 + F, 0, 0, 0, 2 * k⟩ [fm]⊢⁺ ⟨13 * k + 11 + F, 0, 0, 0, 18 * k + 18⟩ :=
  stepPlus_trans even_trans odd_trans

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, F⟩ ↦ ⟨k + 1 + F, 0, 0, 0, 2 * k⟩) ⟨0, 0⟩
  intro ⟨k, F⟩
  refine ⟨⟨9 * k + 9, 4 * k + 1 + F⟩, ?_⟩
  show ⟨k + 1 + F, 0, 0, 0, 2 * k⟩ [fm]⊢⁺ ⟨(9 * k + 9) + 1 + (4 * k + 1 + F), 0, 0, 0, 2 * (9 * k + 9)⟩
  rw [show (9 * k + 9) + 1 + (4 * k + 1 + F) = 13 * k + 11 + F from by ring,
      show 2 * (9 * k + 9) = 18 * k + 18 from by ring]
  exact main_trans
