import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1999: [99/35, 5/6, 88/5, 7/11, 5/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  1  0  0
 3  0 -1  0  1
 0  0  0  1 -1
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1999

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r3_chain : ∀ C, ⟨a, 0, C, 0, e⟩ [fm]⊢* ⟨a + 3 * C, 0, 0, 0, e + C⟩ := by
  intro C; induction' C with C ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 3) (e := e + 1))
    ring_nf; finish

theorem r1r2_chain : ∀ D, ⟨A + D, B, 1, D, E⟩ [fm]⊢* ⟨A, B + D, 1, 0, E + D⟩ := by
  intro D; induction' D with D ih generalizing A B E
  · exists 0
  · rw [show A + (D + 1) = A + D + 1 from by ring]
    step fm
    rw [show A + D + 1 = (A + D) + 1 from by ring,
        show B + 2 = (B + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A := A) (B := B + 1) (E := E + 1))
    ring_nf; finish

theorem drain : ∀ B, ⟨A, B, C + 1, 0, E⟩ [fm]⊢* ⟨A + 2 * B + 3 * C + 3, 0, 0, 0, E + C + 1 + B⟩ := by
  intro B; induction' B with B ih generalizing A C E
  · apply stepStar_trans (r3_chain (C + 1) (a := A) (e := E))
    ring_nf; finish
  · rcases A with _ | A
    · step fm
      step fm
      apply stepStar_trans (ih (A := 2) (C := C) (E := E + 1))
      ring_nf; finish
    · step fm
      apply stepStar_trans (ih (A := A) (C := C + 1) (E := E))
      ring_nf; finish

theorem main_trans : ⟨d + k + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2 * d + k + 3, 0, 0, 2 * d + 1, 0⟩ := by
  step fm
  rw [show d + k = k + d from by ring]
  apply stepStar_trans (r1r2_chain d (A := k) (B := 0) (E := 0))
  show ⟨k, 0 + d, 1, 0, 0 + d⟩ [fm]⊢* ⟨2 * d + k + 3, 0, 0, 2 * d + 1, 0⟩
  rw [show (0 : ℕ) + d = d from by ring]
  apply stepStar_trans (drain d (A := k) (C := 0) (E := d))
  rw [show k + 2 * d + 3 * 0 + 3 = 2 * d + k + 3 from by ring,
      show d + 0 + 1 + d = 2 * d + 1 from by ring]
  apply stepStar_trans (e_to_d (2 * d + 1) (a := 2 * d + k + 3) (d := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, d⟩ ↦ ⟨d + k + 1, 0, 0, d, 0⟩) ⟨0, 0⟩
  intro ⟨k, d⟩
  refine ⟨⟨k + 1, 2 * d + 1⟩, ?_⟩
  show ⟨d + k + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2 * d + 1 + (k + 1) + 1, 0, 0, 2 * d + 1, 0⟩
  rw [show 2 * d + 1 + (k + 1) + 1 = 2 * d + k + 3 from by ring]
  exact main_trans

end Sz22_2003_unofficial_1999
