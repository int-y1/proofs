import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1727: [8/15, 33/14, 25/2, 7/11, 21/5]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1727

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih a (c + 2) e)
  rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]; finish

theorem r4_chain : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show (k : ℕ) + 1 = k + 1 from rfl]; step fm
  apply stepStar_trans (ih c (d + 1))
  rw [show d + 1 + k = d + (k + 1) from by ring]; finish

theorem r2r1_chain : ∀ k, ∀ A C D E,
    ⟨A + 1, 0, C + k, D + k, E⟩ [fm]⊢* ⟨A + 2 * k + 1, 0, C, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring,
      show D + (k + 1) = (D + k) + 1 from by ring]
  step fm; step fm
  rw [show A + 3 = (A + 2) + 1 from by ring]
  apply stepStar_trans (ih (A + 2) C D (E + 1))
  rw [show A + 2 + 2 * k + 1 = A + 2 * (k + 1) + 1 from by ring,
      show E + 1 + k = E + (k + 1) from by ring]; finish

theorem main_trans (n C : ℕ) :
    ⟨0, 0, C + n + 4, 0, n + 1⟩ [fm]⊢⁺ ⟨0, 0, C + n + 4 + 3 * n + 10, 0, n + 2⟩ := by
  have p1 : ⟨0, 0, C + n + 4, 0, n + 1⟩ [fm]⊢*
      ⟨0, 0, C + n + 4, n + 1, 0⟩ := by
    have h := r4_chain (n + 1) (C + n + 4) 0
    simp at h; exact h
  have p2 : ⟨0, 0, C + n + 4, n + 1, 0⟩ [fm]⊢⁺
      ⟨3, 0, C + n + 2, n + 2, 0⟩ := by
    rw [show C + n + 4 = (C + n + 3) + 1 from by ring]
    step fm
    rw [show C + n + 3 = (C + n + 2) + 1 from by ring]
    step fm; finish
  have p3 : ⟨3, 0, C + n + 2, n + 2, 0⟩ [fm]⊢*
      ⟨2 * n + 7, 0, C, 0, n + 2⟩ := by
    have h := r2r1_chain (n + 2) 2 C 0 0
    rw [show 2 + 2 * (n + 2) + 1 = 2 * n + 7 from by ring,
        show (0 : ℕ) + (n + 2) = n + 2 from by ring,
        show C + (n + 2) = C + n + 2 from by ring] at h
    rw [show (3 : ℕ) = 2 + 1 from by ring]; exact h
  have p4 : ⟨2 * n + 7, 0, C, 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, C + 2 * (2 * n + 7), 0, n + 2⟩ := by
    have h := r3_chain (2 * n + 7) 0 C (n + 2)
    simp at h; exact h
  have goal_rw : C + 2 * (2 * n + 7) = C + n + 4 + 3 * n + 10 := by ring
  rw [goal_rw] at p4
  exact stepPlus_stepStar_stepPlus
    (stepStar_stepPlus_stepPlus p1 p2)
    (stepStar_trans p3 p4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 9, 0, 1⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, C⟩ ↦ ⟨0, 0, C + n + 4, 0, n + 1⟩) ⟨0, 5⟩
  intro ⟨n, C⟩
  refine ⟨⟨n + 1, C + 3 * n + 9⟩, ?_⟩
  show ⟨0, 0, C + n + 4, 0, n + 1⟩ [fm]⊢⁺ ⟨0, 0, (C + 3 * n + 9) + (n + 1) + 4, 0, (n + 1) + 1⟩
  rw [show (C + 3 * n + 9) + (n + 1) + 4 = C + n + 4 + 3 * n + 10 from by ring]
  exact main_trans n C

end Sz22_2003_unofficial_1727
