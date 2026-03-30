import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1051: [5/12, 49/2, 6/35, 11/7, 20/11]

Vector representation:
```
-2 -1  1  0  0
-1  0  0  2  0
 1  1 -1 -1  0
 0  0  0 -1  1
 2  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1051

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

theorem r1r5_chain : ∀ k, ∀ C F,
    ⟨(2 : ℕ), k + 1, C, 0, F + (k + 1)⟩ [fm]⊢* ⟨2, 0, C + 2 * (k + 1), 0, F⟩ := by
  intro k; induction' k with k ih <;> intro C F
  · step fm; step fm; ring_nf; finish
  · rw [show C + 2 * (k + 1 + 1) = (C + 2) + 2 * (k + 1) from by ring,
        show F + (k + 1 + 1) = F + (k + 1) + 1 from by ring]
    step fm; step fm
    exact ih (C + 2) F

theorem r3r2_chain : ∀ k, ∀ B D E,
    ⟨(0 : ℕ), B, k, D + 1, E⟩ [fm]⊢* ⟨0, B + k, 0, D + k + 1, E⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · ring_nf; finish
  · rw [show D + (k + 1) + 1 = (D + 1) + k + 1 from by ring,
        show B + (k + 1) = (B + 1) + k from by ring]
    step fm; step fm
    exact ih (B + 1) (D + 1) E

theorem r4_drain : ∀ k, ∀ B E,
    ⟨(0 : ℕ), B, 0, k, E⟩ [fm]⊢* ⟨0, B, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro B E
  · ring_nf; finish
  · rw [show E + (k + 1) = (E + 1) + k from by ring]
    step fm
    exact ih B (E + 1)

theorem main_trans (B F : ℕ) :
    ⟨(0 : ℕ), B + 1, 0, 0, B + F + 2⟩ [fm]⊢⁺
    ⟨0, 2 * B + 3, 0, 0, 2 * B + F + 7⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, B + 1, 0, 0, B + F + 2⟩ = some ⟨2, B + 1, 1, 0, B + F + 1⟩
    rw [show B + F + 2 = (B + F + 1) + 1 from by ring]
    unfold fm; simp only
  apply stepStar_trans
  · show ⟨(2 : ℕ), B + 1, 1, 0, B + F + 1⟩ [fm]⊢* ⟨2, 0, 2 * B + 3, 0, F⟩
    rw [show B + F + 1 = F + (B + 1) from by ring]
    have h := r1r5_chain B 1 F
    convert h using 2; all_goals ring_nf
  apply stepStar_trans
  · show ⟨(2 : ℕ), 0, 2 * B + 3, 0, F⟩ [fm]⊢* ⟨0, 0, 2 * B + 3, 4, F⟩
    step fm; step fm; ring_nf; finish
  apply stepStar_trans
  · show ⟨(0 : ℕ), 0, 2 * B + 3, 4, F⟩ [fm]⊢* ⟨0, 2 * B + 3, 0, 2 * B + 7, F⟩
    rw [show (4 : ℕ) = 3 + 1 from by ring]
    have h := r3r2_chain (2 * B + 3) 0 3 F
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  show ⟨(0 : ℕ), 2 * B + 3, 0, 2 * B + 7, F⟩ [fm]⊢* ⟨0, 2 * B + 3, 0, 0, 2 * B + F + 7⟩
  have h := r4_drain (2 * B + 7) (2 * B + 3) F
  convert h using 2; all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 6⟩) (by execute fm 13)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨B, F⟩ ↦ ⟨0, B + 1, 0, 0, B + F + 2⟩) ⟨0, 4⟩
  intro ⟨B, F⟩
  exact ⟨⟨2 * B + 2, F + 3⟩, by
    show ⟨(0 : ℕ), B + 1, 0, 0, B + F + 2⟩ [fm]⊢⁺
      ⟨0, 2 * B + 2 + 1, 0, 0, (2 * B + 2) + (F + 3) + 2⟩
    rw [show 2 * B + 2 + 1 = 2 * B + 3 from by ring,
        show (2 * B + 2) + (F + 3) + 2 = 2 * B + F + 7 from by ring]
    exact main_trans B F⟩

end Sz22_2003_unofficial_1051
