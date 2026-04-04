import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1742: [8/15, 33/14, 65/2, 7/11, 22/13]

Vector representation:
```
 3 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 1  0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1742

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | _ => none

theorem r3_chain : ∀ n, ⟨n, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + n, 0, e, f + n⟩ := by
  intro n; induction' n with n ih generalizing c e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 1) (f := f + 1))
    ring_nf; finish

theorem r4_chain : ∀ n, ⟨0, 0, c, d, n, f⟩ [fm]⊢* ⟨0, 0, c, d + n, 0, f⟩ := by
  intro n; induction' n with n ih generalizing c d f
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ d, ⟨a + 1, 0, c + d, d, e, f⟩ [fm]⊢* ⟨a + 2 * d + 1, 0, c, 0, e + d, f⟩ := by
  intro d; induction' d with d ih generalizing a c e f
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

theorem main_trans (k T : ℕ) :
    ⟨2 * k + 3, 0, T + 1, 0, k + 2, 2 * T⟩ [fm]⊢⁺
    ⟨2 * k + 5, 0, T + k + 2, 0, k + 3, 2 * T + 2 * k + 2⟩ := by
  step fm
  apply stepStar_trans (r3_chain (2 * k + 2) (c := T + 2) (e := k + 2) (f := 2 * T + 1))
  rw [show T + 2 + (2 * k + 2) = T + 2 * k + 4 from by ring,
      show 2 * T + 1 + (2 * k + 2) = 2 * T + 2 * k + 3 from by ring]
  apply stepStar_trans (r4_chain (k + 2) (c := T + 2 * k + 4) (d := 0) (f := 2 * T + 2 * k + 3))
  rw [show 0 + (k + 2) = k + 2 from by ring]
  rw [show (2 * T + 2 * k + 3 : ℕ) = (2 * T + 2 * k + 2) + 1 from by ring]
  step fm
  rw [show T + 2 * k + 4 = (T + k + 2) + (k + 2) from by ring]
  apply stepStar_trans (r2r1_chain (k + 2) (a := 0) (c := T + k + 2) (e := 1) (f := 2 * T + 2 * k + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 1, 0, 2, 0⟩)
  · execute fm 7
  · apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
      (fun ⟨k, T⟩ ↦ ⟨2 * k + 3, 0, T + 1, 0, k + 2, 2 * T⟩) ⟨0, 0⟩
    intro ⟨k, T⟩
    refine ⟨⟨k + 1, T + k + 1⟩, ?_⟩
    show ⟨2 * k + 3, 0, T + 1, 0, k + 2, 2 * T⟩ [fm]⊢⁺
         ⟨2 * (k + 1) + 3, 0, (T + k + 1) + 1, 0, (k + 1) + 2, 2 * (T + k + 1)⟩
    rw [show 2 * (k + 1) + 3 = 2 * k + 5 from by ring,
        show (T + k + 1) + 1 = T + k + 2 from by ring,
        show (k + 1) + 2 = k + 3 from by ring,
        show 2 * (T + k + 1) = 2 * T + 2 * k + 2 from by ring]
    exact main_trans k T
