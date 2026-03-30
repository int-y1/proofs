import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1047: [45/2, 66/35, 1/5, 7/99, 22/3]

Vector representation:
```
-1  2  1  0  0
 1  1 -1 -1  1
 0  0 -1  0  0
 0 -2  0  1 -1
 1 -1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1047

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+2, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem r1r2_chain : ∀ k, ∀ B e,
    ⟨(1 : ℕ), B, 0, k, e⟩ [fm]⊢* ⟨1, B + 3 * k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro B e
  · ring_nf; finish
  · rw [show B + 3 * (k + 1) = (B + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; step fm
    exact ih (B + 3) (e + 1)

theorem r4_chain : ∀ k, ∀ B d,
    ⟨(0 : ℕ), B + 2 * k, 0, d, k⟩ [fm]⊢* ⟨0, B, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro B d
  · finish
  · rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih B (d + 1)

theorem main_trans (B n : ℕ) :
    ⟨(1 : ℕ), B, 0, n + 1, 1⟩ [fm]⊢⁺ ⟨1, B + n, 0, n + 2, 1⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨1, B, 0, n + 1, 1⟩ = some ⟨0, B + 2, 1, n + 1, 1⟩
    unfold fm; simp only
  apply stepStar_trans
  · show ⟨(0 : ℕ), B + 2, 1, n + 1, 1⟩ [fm]⊢* ⟨1, B + 3, 0, n, 2⟩
    step fm; ring_nf; finish
  apply stepStar_trans
  · exact r1r2_chain n (B + 3) 2
  apply stepStar_trans
  · show ⟨(1 : ℕ), B + 3 + 3 * n, 0, 0, 2 + n⟩ [fm]⊢*
        ⟨0, B + 3 * n + 5, 1, 0, 2 + n⟩
    step fm; ring_nf; finish
  apply stepStar_trans
  · show ⟨(0 : ℕ), B + 3 * n + 5, 1, 0, 2 + n⟩ [fm]⊢*
        ⟨0, B + 3 * n + 5, 0, 0, 2 + n⟩
    step fm; ring_nf; finish
  apply stepStar_trans
  · show ⟨(0 : ℕ), B + 3 * n + 5, 0, 0, 2 + n⟩ [fm]⊢*
        ⟨0, B + n + 1, 0, 2 + n, 0⟩
    have := r4_chain (2 + n) (B + n + 1) 0
    convert this using 2; ring_nf
  rw [show B + n + 1 = (B + n) + 1 from by ring,
      show 2 + n = n + 2 from by ring]
  step fm; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 1⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨B, n⟩ ↦ ⟨1, B, 0, n + 1, 1⟩) ⟨0, 0⟩
  intro ⟨B, n⟩
  exact ⟨⟨B + n, n + 1⟩, main_trans B n⟩

end Sz22_2003_unofficial_1047
