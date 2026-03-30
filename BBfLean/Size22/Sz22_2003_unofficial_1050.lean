import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1050: [5/12, 147/2, 2/35, 11/7, 20/11]

Vector representation:
```
-2 -1  1  0  0
-1  1  0  2  0
 1  0 -1 -1  0
 0  0  0 -1  1
 2  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1050

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

theorem r3r2_chain : ∀ k b d e,
    ⟨(0 : ℕ), b, k + 1, d + 1, e⟩ [fm]⊢* ⟨0, b + k + 1, 0, d + k + 2, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · step fm; step fm; ring_nf; finish
  · rw [show b + (k + 1) + 1 = (b + 1) + k + 1 from by ring,
        show d + (k + 1) + 2 = (d + 1) + k + 2 from by ring]
    step fm; step fm
    exact ih (b + 1) (d + 1) e

theorem r4_drain : ∀ k b e,
    ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨0, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show e + (k + 1) = (e + 1) + k from by ring]
    step fm
    exact ih b (e + 1)

theorem r5r1_chain : ∀ k c e,
    ⟨(0 : ℕ), k + 1, c, 0, e + k + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * k + 2, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · step fm; step fm; ring_nf; finish
  · rw [show c + 2 * (k + 1) + 2 = (c + 2) + 2 * k + 2 from by ring,
        show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring]
    step fm; step fm
    rw [show c + 1 + 1 = c + 2 from by ring,
        show e + 1 + k = e + k + 1 from by ring]
    exact ih (c + 2) e

theorem main_trans (C E : ℕ) :
    ⟨(0 : ℕ), 0, C, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 2 * C + 6, 0, E + 2⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, C, 0, E + 1⟩ = some ⟨2, 0, C + 1, 0, E⟩
    unfold fm; simp only
  apply stepStar_trans
  · show ⟨(2 : ℕ), 0, C + 1, 0, E⟩ [fm]⊢* ⟨0, 2, C + 1, 4, E⟩
    step fm; step fm; ring_nf; finish
  apply stepStar_trans
  · show ⟨(0 : ℕ), 2, C + 1, 4, E⟩ [fm]⊢* ⟨0, C + 3, 0, C + 5, E⟩
    convert r3r2_chain C 2 3 E using 2; ring_nf
  apply stepStar_trans
  · show ⟨(0 : ℕ), C + 3, 0, C + 5, E⟩ [fm]⊢* ⟨0, C + 3, 0, 0, E + (C + 5)⟩
    exact r4_drain (C + 5) (C + 3) E
  · show ⟨(0 : ℕ), C + 3, 0, 0, E + (C + 5)⟩ [fm]⊢* ⟨0, 0, 2 * C + 6, 0, E + 2⟩
    convert r5r1_chain (C + 2) 0 (E + 2) using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨C, E⟩ ↦ ⟨0, 0, C, 0, E + 1⟩) ⟨2, 0⟩
  intro ⟨C, E⟩
  exact ⟨⟨2 * C + 6, E + 1⟩, main_trans C E⟩

end Sz22_2003_unofficial_1050
