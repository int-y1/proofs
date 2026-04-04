import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1960: [945/2, 4/55, 1/5, 11/63, 5/3]

Vector representation:
```
-1  3  1  1  0
 2  0 -1  0 -1
 0  0 -1  0  0
 0 -2  0 -1  1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1960

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k b d e, ⟨0, b + 2 * k, 0, d + k, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ (e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k b c d, ⟨0, b, c + k, d, 0⟩ [fm]⊢* ⟨0, b, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    finish

theorem spiral : ∀ k b c d, ⟨0, b, c + 1, d, k + 1⟩ [fm]⊢* ⟨0, b + 6 * (k + 1), c + k + 2, d + 2 * (k + 1), 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · step fm; step fm; step fm; finish
  · rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
    step fm; step fm; step fm
    show ⟨0, b + 6, (c + 1) + 1, d + 2, k + 1⟩ [fm]⊢* _
    apply stepStar_trans (ih (b + 6) (c + 1) (d + 2))
    ring_nf; finish

theorem phase_r4 : ∀ D F, ⟨0, 2 * D + F + 3, 0, D + 1, 0⟩ [fm]⊢* ⟨0, F + 1, 0, 0, D + 1⟩ := by
  intro D F
  have h := r4_chain (D + 1) (F + 1) 0 0
  simp only [Nat.zero_add] at h
  rw [show F + 1 + 2 * (D + 1) = 2 * D + F + 3 from by ring] at h
  exact h

theorem phase_mid : ⟨0, F + 1, 0, 0, D + 1⟩ [fm]⊢* ⟨0, F + 6, 2, 2, D⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem phase_spiral_r3 : ∀ D, ⟨0, F + 6, 2, 2, D + 1⟩ [fm]⊢* ⟨0, 6 * D + F + 12, 0, 2 * D + 4, 0⟩ := by
  intro D
  show ⟨0, F + 6, 1 + 1, 2, D + 1⟩ [fm]⊢* _
  apply stepStar_trans (spiral D (F + 6) 1 2)
  rw [show F + 6 + 6 * (D + 1) = 6 * D + F + 12 from by ring,
      show 1 + D + 2 = 0 + (D + 3) from by ring,
      show 2 + 2 * (D + 1) = 2 * D + 4 from by ring]
  exact r3_chain (D + 3) _ 0 _

theorem main_trans : ∀ D F, ⟨0, 2 * D + F + 3, 0, D + 1, 0⟩ [fm]⊢⁺ ⟨0, 6 * D + F + 6, 0, 2 * D + 2, 0⟩ := by
  intro D F; rcases D with _ | D
  · -- D = 0
    step fm
    step fm; step fm; step fm; step fm
    step fm; step fm; finish
  · -- D >= 1
    apply stepStar_stepPlus_stepPlus (phase_r4 (D + 1) F)
    apply stepStar_stepPlus_stepPlus (phase_mid (F := F) (D := D + 1))
    show ⟨0, F + 6, 2, 2, D + 1⟩ [fm]⊢⁺ ⟨0, 6 * (D + 1) + F + 6, 0, 2 * (D + 1) + 2, 0⟩
    rw [show 6 * (D + 1) + F + 6 = 6 * D + F + 12 from by ring,
        show 2 * (D + 1) + 2 = 2 * D + 4 from by ring]
    show ⟨0, F + 6, 1 + 1, 2, D + 1⟩ [fm]⊢⁺ _
    step fm; step fm; step fm
    show ⟨0, F + 12, 1 + 1 + 1, 2 + 2, D⟩ [fm]⊢* _
    rcases D with _ | D
    · rw [show F + 12 = 6 * 0 + F + 12 from by ring,
          show (1 : ℕ) + 1 + 1 = 0 + 3 from by ring,
          show (2 : ℕ) + 2 = 2 * 0 + 4 from by ring]
      exact r3_chain 3 _ 0 _
    · show ⟨0, F + 12, (1 + 1) + 1, 2 + 2, D + 1⟩ [fm]⊢* _
      apply stepStar_trans (spiral D (F + 12) (1 + 1) (2 + 2))
      rw [show F + 12 + 6 * (D + 1) = 6 * (D + 1) + F + 12 from by ring,
          show 1 + 1 + D + 2 = 0 + (D + 4) from by ring,
          show 2 + 2 + 2 * (D + 1) = 2 * (D + 1) + 4 from by ring]
      exact r3_chain (D + 4) _ 0 _

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, F⟩ ↦ ⟨0, 2 * D + F + 3, 0, D + 1, 0⟩) ⟨0, 0⟩
  intro ⟨D, F⟩
  refine ⟨⟨2 * D + 1, F + 2 * D + 1⟩, ?_⟩
  show ⟨0, 2 * D + F + 3, 0, D + 1, 0⟩ [fm]⊢⁺
    ⟨0, 2 * (2 * D + 1) + (F + 2 * D + 1) + 3, 0, (2 * D + 1) + 1, 0⟩
  rw [show 2 * (2 * D + 1) + (F + 2 * D + 1) + 3 = 6 * D + F + 6 from by ring,
      show (2 * D + 1) + 1 = 2 * D + 2 from by ring]
  exact main_trans D F
