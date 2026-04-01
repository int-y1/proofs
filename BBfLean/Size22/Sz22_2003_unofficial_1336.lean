import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1336: [63/10, 2/33, 1573/2, 5/7, 10/13]

Vector representation:
```
-1  2 -1  1  0  0
 1 -1  0  0 -1  0
-1  0  0  0  2  1
 0  0  1 -1  0  0
 1  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1336

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c+1, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih generalizing a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e + 2) (f := f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨0, 0, c, d + k, e, f⟩ [fm]⊢* ⟨0, 0, c + k, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing c d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ⟨a, b + k, 0, d, e + k, f⟩ [fm]⊢* ⟨a + k, b, 0, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing a b d e f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

theorem r1r2_spiral : ∀ k, ⟨1, b, k, d, e + k, f⟩ [fm]⊢* ⟨1, b + k, 0, d + k, e, f⟩ := by
  intro k; induction' k with k ih generalizing b d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d + 1))
    ring_nf; finish

theorem phases12 : ⟨n + 2, 0, 0, n + 1, 0, F⟩ [fm]⊢* ⟨0, 0, n + 1, 0, 2 * n + 4, F + n + 2⟩ := by
  apply stepStar_trans
  · rw [show n + 2 = 0 + (n + 2) from by ring]
    exact r3_chain (n + 2) (a := 0) (d := n + 1) (e := 0) (f := F)
  rw [show (0 : ℕ) + 2 * (n + 2) = 2 * n + 4 from by ring,
      show F + (n + 2) = F + n + 2 from by ring]
  apply stepStar_trans
  · rw [show (n + 1 : ℕ) = 0 + (n + 1) from by ring]
    exact r4_chain (n + 1) (c := 0) (d := 0) (e := 2 * n + 4) (f := F + n + 2)
  rw [show (0 : ℕ) + (n + 1) = n + 1 from by ring]
  finish

theorem phases345 : ⟨0, 0, n + 1, 0, 2 * n + 4, F + n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 2, 0, F + n + 1⟩ := by
  rw [show F + n + 2 = (F + n + 1) + 1 from by ring]
  step fm
  rw [show 2 * n + 4 = (n + 2) + (n + 2) from by ring]
  apply stepStar_trans
  · rw [show (n + 2) + (n + 2) = (0 + (n + 2)) + (n + 2) from by ring]
    exact r1r2_spiral (n + 2) (b := 0) (d := 0) (e := 0 + (n + 2)) (f := F + n + 1)
  apply stepStar_trans (r2_drain (n + 2) (a := 1) (b := 0) (d := 0 + (n + 2)) (e := 0) (f := F + n + 1))
  ring_nf; finish

theorem main_trans : ⟨n + 2, 0, 0, n + 1, 0, F⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 2, 0, F + n + 1⟩ :=
  stepStar_stepPlus_stepPlus phases12 phases345

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 0⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, F⟩ ↦ ⟨n + 2, 0, 0, n + 1, 0, F⟩) ⟨0, 0⟩
  intro ⟨n, F⟩
  exact ⟨⟨n + 1, F + n + 1⟩, main_trans⟩

end Sz22_2003_unofficial_1336
