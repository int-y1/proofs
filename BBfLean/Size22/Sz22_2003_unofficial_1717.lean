import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1717: [77/45, 14/5, 25/22, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  1  1
 1  0 -1  1  0
-1  0  2  0 -1
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1717

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k a b d,
    ⟨a, b, 0, d + k, 0⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (b + 1) d); ring_nf; finish

theorem r1r1r3_chain : ∀ J a B d e,
    ⟨a + J, B + 4 * J, 2, d, e⟩ [fm]⊢* ⟨a, B, 2, d + 2 * J, e + J⟩ := by
  intro J; induction' J with J ih <;> intro a B d e
  · simp; exists 0
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a + J + 1, B + 4 * J + 4, 2, d, e⟩ = some ⟨a + J + 1, B + 4 * J + 2, 1, d + 1, e + 1⟩
    simp [fm]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a + J + 1, B + 4 * J + 2, 1, d + 1, e + 1⟩ = some ⟨a + J + 1, B + 4 * J, 0, d + 2, e + 2⟩
    simp [fm]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a + J + 1, B + 4 * J, 0, d + 2, e + 2⟩ = some ⟨a + J, B + 4 * J, 2, d + 2, e + 1⟩
    simp [fm]
  convert ih a B (d + 2) (e + 1) using 1; ring_nf

theorem r3r2r2_b0 : ∀ k a d,
    ⟨a + 1, 0, 0, d, k⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · simp; exists 0
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a + 1, 0, 0, d, k + 1⟩ = some ⟨a, 0, 2, d, k⟩
    simp [fm]
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm; step fm
  rw [show a + 1 + 1 = (a + 1) + 1 from by ring,
      show d + 1 + 1 = d + 2 from by ring]
  apply stepStar_trans (ih (a + 1) (d + 2))
  rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
      show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]; finish

theorem r3r2r2_b1 : ∀ k a d,
    ⟨a + 1, 1, 0, d, k⟩ [fm]⊢* ⟨a + k + 1, 1, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · simp; exists 0
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a + 1, 1, 0, d, k + 1⟩ = some ⟨a, 1, 2, d, k⟩
    simp [fm]
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm; step fm
  rw [show a + 1 + 1 = (a + 1) + 1 from by ring,
      show d + 1 + 1 = d + 2 from by ring]
  apply stepStar_trans (ih (a + 1) (d + 2))
  rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
      show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]; finish

theorem closing : ∀ a b,
    ⟨a + 3, b + 2, 0, 0, 0⟩ [fm]⊢* ⟨a + 1, b, 2, 1, 1⟩ := by
  intro a b
  rw [show a + 3 = (a + 2) + 1 from by ring]
  step fm
  rw [show b + 2 = b + 2 from rfl, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a + 2, b, 0, 1, 2⟩ = some ⟨a + 1, b, 2, 1, 1⟩
    simp [fm]
  finish

theorem main_trans_mod1 (j : ℕ) :
    ⟨4*j+1, 12*j+4, 2, 1, 1⟩ [fm]⊢⁺ ⟨4*j+2, 12*j+7, 2, 1, 1⟩ := by
  apply step_stepStar_stepPlus (by
    show fm ⟨4*j+1, 12*j+4, 2, 1, 1⟩ = some ⟨4*j+1, 12*j+2, 1, 2, 2⟩; simp [fm])
  apply stepStar_trans (step_stepStar (by
    show fm ⟨4*j+1, 12*j+2, 1, 2, 2⟩ = some ⟨4*j+1, 12*j, 0, 3, 3⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by
    show fm ⟨4*j+1, 12*j, 0, 3, 3⟩ = some ⟨4*j, 12*j, 2, 3, 2⟩; simp [fm]))
  have h1 : ⟨4*j, 12*j, 2, 3, 2⟩ [fm]⊢* ⟨j, 0, 2, 6*j+3, 3*j+2⟩ := by
    have := r1r1r3_chain (3*j) j 0 3 2
    convert this using 1; ring_nf
  apply stepStar_trans h1
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm; step fm
  rw [show j + 1 + 1 = (j + 1) + 1 from by ring,
      show 6 * j + 3 + 1 + 1 = 6 * j + 5 from by ring]
  apply stepStar_trans (r3r2r2_b0 (3*j+2) (j+1) (6*j+5))
  rw [show j + 1 + (3 * j + 2) + 1 = 4 * j + 4 from by ring,
      show 6 * j + 5 + 2 * (3 * j + 2) = 12 * j + 9 from by ring,
      show 12 * j + 9 = 0 + (12 * j + 9) from by ring]
  apply stepStar_trans (r4_chain (12*j+9) (4*j+4) 0 0)
  rw [show 0 + (12 * j + 9) = 12 * j + 9 from by ring,
      show 4 * j + 4 = (4 * j + 1) + 3 from by ring,
      show 12 * j + 9 = (12 * j + 7) + 2 from by ring]
  exact closing (4*j+1) (12*j+7)

theorem main_trans_mod2 (j : ℕ) :
    ⟨4*j+2, 12*j+7, 2, 1, 1⟩ [fm]⊢⁺ ⟨4*j+3, 12*j+10, 2, 1, 1⟩ := by
  apply step_stepStar_stepPlus (by
    show fm ⟨4*j+2, 12*j+7, 2, 1, 1⟩ = some ⟨4*j+2, 12*j+5, 1, 2, 2⟩; simp [fm])
  apply stepStar_trans (step_stepStar (by
    show fm ⟨4*j+2, 12*j+5, 1, 2, 2⟩ = some ⟨4*j+2, 12*j+3, 0, 3, 3⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by
    show fm ⟨4*j+2, 12*j+3, 0, 3, 3⟩ = some ⟨4*j+1, 12*j+3, 2, 3, 2⟩; simp [fm]))
  have h1 : ⟨4*j+1, 12*j+3, 2, 3, 2⟩ [fm]⊢* ⟨j+1, 3, 2, 6*j+3, 3*j+2⟩ := by
    have := r1r1r3_chain (3*j) (j+1) 3 3 2
    convert this using 1; ring_nf
  apply stepStar_trans h1
  apply stepStar_trans (step_stepStar (by
    show fm ⟨j+1, 3, 2, 6*j+3, 3*j+2⟩ = some ⟨j+1, 1, 1, 6*j+4, 3*j+3⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by
    show fm ⟨j+1, 1, 1, 6*j+4, 3*j+3⟩ = some ⟨j+2, 1, 0, 6*j+5, 3*j+3⟩; simp [fm]))
  apply stepStar_trans (r3r2r2_b1 (3*j+3) (j+1) (6*j+5))
  rw [show j + 1 + (3 * j + 3) + 1 = 4 * j + 5 from by ring,
      show 6 * j + 5 + 2 * (3 * j + 3) = 12 * j + 11 from by ring,
      show 12 * j + 11 = 0 + (12 * j + 11) from by ring]
  apply stepStar_trans (r4_chain (12*j+11) (4*j+5) 1 0)
  rw [show 1 + (12 * j + 11) = 12 * j + 12 from by ring,
      show 4 * j + 5 = (4 * j + 2) + 3 from by ring,
      show 12 * j + 12 = (12 * j + 10) + 2 from by ring]
  exact closing (4*j+2) (12*j+10)

theorem main_trans_mod3 (j : ℕ) :
    ⟨4*j+3, 12*j+10, 2, 1, 1⟩ [fm]⊢⁺ ⟨4*j+4, 12*j+13, 2, 1, 1⟩ := by
  apply step_stepStar_stepPlus (by
    show fm ⟨4*j+3, 12*j+10, 2, 1, 1⟩ = some ⟨4*j+3, 12*j+8, 1, 2, 2⟩; simp [fm])
  apply stepStar_trans (step_stepStar (by
    show fm ⟨4*j+3, 12*j+8, 1, 2, 2⟩ = some ⟨4*j+3, 12*j+6, 0, 3, 3⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by
    show fm ⟨4*j+3, 12*j+6, 0, 3, 3⟩ = some ⟨4*j+2, 12*j+6, 2, 3, 2⟩; simp [fm]))
  have h1 : ⟨4*j+2, 12*j+6, 2, 3, 2⟩ [fm]⊢* ⟨j+1, 2, 2, 6*j+5, 3*j+3⟩ := by
    have := r1r1r3_chain (3*j+1) (j+1) 2 3 2
    convert this using 1; ring_nf
  apply stepStar_trans h1
  apply stepStar_trans (step_stepStar (by
    show fm ⟨j+1, 2, 2, 6*j+5, 3*j+3⟩ = some ⟨j+1, 0, 1, 6*j+6, 3*j+4⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by
    show fm ⟨j+1, 0, 1, 6*j+6, 3*j+4⟩ = some ⟨j+2, 0, 0, 6*j+7, 3*j+4⟩; simp [fm]))
  apply stepStar_trans (r3r2r2_b0 (3*j+4) (j+1) (6*j+7))
  rw [show j + 1 + (3 * j + 4) + 1 = 4 * j + 6 from by ring,
      show 6 * j + 7 + 2 * (3 * j + 4) = 12 * j + 15 from by ring,
      show 12 * j + 15 = 0 + (12 * j + 15) from by ring]
  apply stepStar_trans (r4_chain (12*j+15) (4*j+6) 0 0)
  rw [show 0 + (12 * j + 15) = 12 * j + 15 from by ring,
      show 4 * j + 6 = (4 * j + 3) + 3 from by ring,
      show 12 * j + 15 = (12 * j + 13) + 2 from by ring]
  exact closing (4*j+3) (12*j+13)

theorem main_trans_mod0 (j : ℕ) :
    ⟨4*j+4, 12*j+13, 2, 1, 1⟩ [fm]⊢⁺ ⟨4*j+5, 12*j+16, 2, 1, 1⟩ := by
  apply step_stepStar_stepPlus (by
    show fm ⟨4*j+4, 12*j+13, 2, 1, 1⟩ = some ⟨4*j+4, 12*j+11, 1, 2, 2⟩; simp [fm])
  apply stepStar_trans (step_stepStar (by
    show fm ⟨4*j+4, 12*j+11, 1, 2, 2⟩ = some ⟨4*j+4, 12*j+9, 0, 3, 3⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by
    show fm ⟨4*j+4, 12*j+9, 0, 3, 3⟩ = some ⟨4*j+3, 12*j+9, 2, 3, 2⟩; simp [fm]))
  have h1 : ⟨4*j+3, 12*j+9, 2, 3, 2⟩ [fm]⊢* ⟨j+1, 1, 2, 6*j+7, 3*j+4⟩ := by
    have := r1r1r3_chain (3*j+2) (j+1) 1 3 2
    convert this using 1; ring_nf
  apply stepStar_trans h1
  apply stepStar_trans (step_stepStar (by
    show fm ⟨j+1, 1, 2, 6*j+7, 3*j+4⟩ = some ⟨j+2, 1, 1, 6*j+8, 3*j+4⟩; simp [fm]))
  apply stepStar_trans (step_stepStar (by
    show fm ⟨j+2, 1, 1, 6*j+8, 3*j+4⟩ = some ⟨j+3, 1, 0, 6*j+9, 3*j+4⟩; simp [fm]))
  apply stepStar_trans (r3r2r2_b1 (3*j+4) (j+2) (6*j+9))
  rw [show j + 2 + (3 * j + 4) + 1 = 4 * j + 7 from by ring,
      show 6 * j + 9 + 2 * (3 * j + 4) = 12 * j + 17 from by ring,
      show 12 * j + 17 = 0 + (12 * j + 17) from by ring]
  apply stepStar_trans (r4_chain (12*j+17) (4*j+7) 1 0)
  rw [show 1 + (12 * j + 17) = 12 * j + 18 from by ring,
      show 4 * j + 7 = (4 * j + 4) + 3 from by ring,
      show 12 * j + 18 = (12 * j + 16) + 2 from by ring]
  exact closing (4*j+4) (12*j+16)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 4, 2, 1, 1⟩) (by execute fm 24)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ j, q = ⟨4*j+1, 12*j+4, 2, 1, 1⟩ ∨
                        q = ⟨4*j+2, 12*j+7, 2, 1, 1⟩ ∨
                        q = ⟨4*j+3, 12*j+10, 2, 1, 1⟩ ∨
                        q = ⟨4*j+4, 12*j+13, 2, 1, 1⟩)
  · intro q ⟨j, hq⟩
    rcases hq with hq | hq | hq | hq
    · subst hq
      exact ⟨_, ⟨j, Or.inr (Or.inl rfl)⟩, main_trans_mod1 j⟩
    · subst hq
      exact ⟨_, ⟨j, Or.inr (Or.inr (Or.inl rfl))⟩, main_trans_mod2 j⟩
    · subst hq
      exact ⟨_, ⟨j, Or.inr (Or.inr (Or.inr rfl))⟩, main_trans_mod3 j⟩
    · subst hq
      refine ⟨_, ⟨j + 1, Or.inl ?_⟩, main_trans_mod0 j⟩
      show (4*j+5, 12*j+16, 2, 1, 1) = (4*(j+1)+1, 12*(j+1)+4, 2, 1, 1)
      ring_nf
  · exact ⟨0, Or.inl (by ring_nf)⟩

end Sz22_2003_unofficial_1717
