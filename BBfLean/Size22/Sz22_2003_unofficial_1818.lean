import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1818: [9/10, 55/21, 4/3, 7/11, 165/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1818

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (b := b))
    ring_nf; finish

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (d := d + 1) (e := e))
    ring_nf; finish

theorem chain : ∀ d, ⟨a + d + 2, b, 1, d + 1, e⟩ [fm]⊢* ⟨a, b + d + 3, 0, 0, e + d + 1⟩ := by
  intro d; induction' d with d ih generalizing a b e
  · step fm; step fm; step fm; finish
  · rw [show a + (d + 1) + 2 = (a + d + 2) + 1 from by ring,
        show (d + 1) + 1 = (d + 1) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a) (b := b + 1) (e := e + 1))
    ring_nf; finish

theorem main_trans : ∀ m D, ⟨m + 2 * D + 3, 0, 0, D + 1, 0⟩ [fm]⊢⁺ ⟨m + 3 * D + 8, 0, 0, D + 2, 0⟩ := by
  intro m D
  rw [show m + 2 * D + 3 = (m + 2 * D + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show ⟨(m + 2 * D + 2) + 1, 0, 0, D + 1, 0⟩ [fm]⊢ ⟨m + 2 * D + 2, 1, 1, D + 1, 1⟩ from rfl)
  rw [show m + 2 * D + 2 = (m + D) + D + 2 from by ring]
  apply stepStar_trans (chain D (a := m + D) (b := 1) (e := 1))
  rw [show 1 + D + 3 = 0 + (D + 4) from by ring]
  apply stepStar_trans (r3_chain (D + 4) (a := m + D) (b := 0) (e := 1 + D + 1))
  rw [show m + D + 2 * (D + 4) = m + 3 * D + 8 from by ring,
      show 1 + D + 1 = 0 + (D + 2) from by ring]
  apply stepStar_trans (e_to_d (D + 2) (a := m + 3 * D + 8) (d := 0) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, D⟩ ↦ ⟨m + 2 * D + 3, 0, 0, D + 1, 0⟩) ⟨2, 0⟩
  intro ⟨m, D⟩
  refine ⟨⟨m + D + 3, D + 1⟩, ?_⟩
  show ⟨m + 2 * D + 3, 0, 0, D + 1, 0⟩ [fm]⊢⁺ ⟨(m + D + 3) + 2 * (D + 1) + 3, 0, 0, (D + 1) + 1, 0⟩
  rw [show (m + D + 3) + 2 * (D + 1) + 3 = m + 3 * D + 8 from by ring,
      show (D + 1) + 1 = D + 2 from by ring]
  exact main_trans m D
