import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1850: [9/35, 1/66, 605/3, 2/5, 147/2]

Vector representation:
```
 0  2 -1 -1  0
-1 -1  0  0 -1
 0 -1  1  0  2
 1  0 -1  0  0
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1850

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

theorem r5r2_chain : ∀ k, ⟨a + 2 * k, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

theorem r1r3_chain : ∀ k, ⟨0, b, 1, k + 1, e⟩ [fm]⊢* ⟨0, b + k + 2, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing b e
  · step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b := b + 1) (e := e + 2))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨0, k, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c := c + 1) (e := e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

theorem tail_star : ⟨0, 0, 1, 2 * n + 2, F + 2⟩ [fm]⊢* ⟨2 * n + 3, 0, 0, 0, F + 8 * n + 10⟩ := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  apply stepStar_trans (r1r3_chain (2 * n + 1) (b := 0) (e := F + 2))
  rw [show 0 + (2 * n + 1) + 2 = 2 * n + 3 from by ring,
      show F + 2 + 2 * (2 * n + 1) = F + 4 * n + 4 from by ring]
  apply stepStar_trans (r3_chain (2 * n + 3) (c := 0) (e := F + 4 * n + 4))
  simp only [Nat.zero_add]
  apply stepStar_trans (r4_chain (2 * n + 3) (a := 0) (e := F + 4 * n + 4 + 2 * (2 * n + 3)))
  ring_nf; finish

theorem main_trans : ⟨2 * n + 1, 0, 0, 0, F + n⟩ [fm]⊢⁺ ⟨2 * n + 3, 0, 0, 0, F + 8 * n + 10⟩ := by
  rw [show 2 * n + 1 = 1 + 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus (r5r2_chain n (a := 1) (d := 0) (e := F))
  simp only [Nat.zero_add]
  step fm; step fm
  exact tail_star

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, F⟩ ↦ ⟨2 * n + 1, 0, 0, 0, F + n⟩) ⟨0, 0⟩
  intro ⟨n, F⟩; exists ⟨n + 1, F + 7 * n + 9⟩
  show ⟨2 * n + 1, 0, 0, 0, F + n⟩ [fm]⊢⁺ ⟨2 * (n + 1) + 1, 0, 0, 0, (F + 7 * n + 9) + (n + 1)⟩
  rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring,
      show (F + 7 * n + 9) + (n + 1) = F + 8 * n + 10 from by ring]
  exact main_trans
