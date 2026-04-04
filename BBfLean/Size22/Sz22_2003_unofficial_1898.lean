import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1898: [9/35, 65/33, 14/3, 11/13, 195/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1898

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c+1, d, e, f+1⟩
  | _ => none

theorem interleave : ∀ k, ∀ B F,
    ⟨a, B + 1, 1, D + k, k, F + 1⟩ [fm]⊢* ⟨a, B + k + 1, 1, D, 0, F + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro B F
  · exists 0
  · rw [show D + (k + 1) = D + k + 1 from by ring]
    step fm
    rw [show B + 1 + 2 = B + 2 + 1 from by ring]
    step fm
    apply stepStar_trans (ih (B + 1) (F + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, k, 0, d, 0, f⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (d := d + 1))
    ring_nf; finish

theorem f_to_e : ∀ k, ⟨a, 0, 0, d, e, k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, 0⟩ := by
  intro k; induction' k with k ih generalizing e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

theorem main_trans : ⟨A + 1, 0, 0, E + K + 1, E, 0⟩ [fm]⊢⁺ ⟨A + E + 3, 0, 0, E + K + 3, E + 1, 0⟩ := by
  step fm
  rw [show E + K + 1 = (K + 1) + E from by ring]
  apply stepStar_trans (interleave E (a := A) (D := K + 1) (B := 0) (F := 0))
  show ⟨A, 0 + E + 1, 1, K + 1, 0, 0 + E + 1⟩ [fm]⊢* _
  rw [show 0 + E + 1 = E + 1 from by ring]
  rw [show K + 1 = K + 0 + 1 from by ring]
  step fm
  show ⟨A, E + 3, 0, K, 0, E + 1⟩ [fm]⊢* ⟨A + E + 3, 0, 0, E + K + 3, E + 1, 0⟩
  apply stepStar_trans (r3_chain (E + 3) (a := A) (d := K) (f := E + 1))
  rw [show A + (E + 3) = A + E + 3 from by ring, show K + (E + 3) = E + K + 3 from by ring]
  apply stepStar_trans (f_to_e (E + 1) (a := A + E + 3) (d := E + K + 3) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A K E, q = ⟨A + 1, 0, 0, E + K + 1, E, 0⟩)
  · intro c ⟨A, K, E, hq⟩; subst hq
    exact ⟨⟨A + E + 3, 0, 0, E + K + 3, E + 1, 0⟩,
      ⟨A + E + 2, K + 1, E + 1, by ring_nf⟩, main_trans⟩
  · exact ⟨2, 0, 1, rfl⟩
