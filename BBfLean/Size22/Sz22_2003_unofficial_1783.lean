import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1783: [9/10, 3773/2, 26/21, 5/13, 3/11]

Vector representation:
```
-1  2 -1  0  0  0
-1  0  0  3  1  0
 1 -1  0 -1  0  1
 0  0  1  0  0 -1
 0  1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1783

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+3, e+1, f⟩
  | ⟨a, b+1, c, d+1, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

theorem f_to_c : ∀ k, ⟨0, 0, c, d, e, k⟩ [fm]⊢* ⟨0, 0, c + k, d, e, 0⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem r3r1_loop : ∀ k, ∀ b d e f,
    ⟨0, b + 1, k, d + k, e, f⟩ [fm]⊢* ⟨0, b + k + 1, 0, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    rw [show b + 1 + 1 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) d e (f + 1))
    ring_nf; finish

theorem r3r2_loop : ∀ k, ∀ d e f,
    ⟨0, k, 0, d + 1, e, f⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k + 1, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (d + 2) (e + 1) (f + 1))
    ring_nf; finish

theorem main_trans (c G E : ℕ) :
    ⟨0, 0, c, c + G + 3, E + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 1, 2 * c + G + 5, E + c + 1, 0⟩ := by
  step fm
  rw [show c + G + 3 = (G + 3) + c from by ring]
  apply stepStar_trans
  · show ⟨0, 0 + 1, c, (G + 3) + c, E, 0⟩ [fm]⊢* ⟨0, 0 + c + 1, 0, G + 3, E, 0 + c⟩
    exact r3r1_loop c 0 (G + 3) E 0
  rw [show (0 : ℕ) + c + 1 = c + 1 from by ring,
      show G + 3 = (G + 2) + 1 from by ring,
      show (0 : ℕ) + c = c from by ring]
  apply stepStar_trans (r3r2_loop (c + 1) (G + 2) E c)
  rw [show G + 2 + 2 * (c + 1) + 1 = 2 * c + G + 5 from by ring,
      show E + (c + 1) = E + c + 1 from by ring,
      show c + (c + 1) = 2 * c + 1 from by ring]
  apply stepStar_trans (f_to_c (2 * c + 1) (c := 0) (d := 2 * c + G + 5) (e := E + c + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨c, G, E⟩ ↦ ⟨0, 0, c, c + G + 3, E + 1, 0⟩) ⟨0, 0, 0⟩
  intro ⟨c, G, E⟩
  refine ⟨⟨2 * c + 1, G + 1, c + E⟩, ?_⟩
  show ⟨0, 0, c, c + G + 3, E + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 1, (2 * c + 1) + (G + 1) + 3, (c + E) + 1, 0⟩
  rw [show (2 * c + 1) + (G + 1) + 3 = 2 * c + G + 5 from by ring,
      show (c + E) + 1 = E + c + 1 from by ring]
  exact main_trans c G E
