import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1704: [77/15, 9/91, 26/3, 5/11, 363/2]

Vector representation:
```
 0 -1 -1  1  1  0
 0  2  0 -1  0 -1
 1 -1  0  0  0  1
 0  0  1  0 -1  0
-1  1  0  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1704

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+2, f⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C F,
    ⟨A, 0, C, 0, k, F⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro A C F
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1) F)
    rw [show C + 1 + k = C + (k + 1) from by ring]; finish

theorem r3_chain : ∀ k, ∀ A E F,
    ⟨A, k, 0, 0, E, F⟩ [fm]⊢* ⟨A + k, 0, 0, 0, E, F + k⟩ := by
  intro k; induction' k with k ih <;> intro A E F
  · exists 0
  · step fm
    apply stepStar_trans (ih (A + 1) E (F + 1))
    rw [show A + 1 + k = A + (k + 1) from by ring,
        show F + 1 + k = F + (k + 1) from by ring]; finish

theorem r2r1r1_chain : ∀ k, ∀ A C D E F,
    ⟨A, 0, C + 2 * k, D + 1, E, F + k⟩ [fm]⊢*
    ⟨A, 0, C, D + k + 1, E + 2 * k, F⟩ := by
  intro k; induction' k with k ih <;> intro A C D E F
  · simp; exists 0
  · rw [show C + 2 * (k + 1) = (C + 2 * k) + 2 from by ring,
        show F + (k + 1) = (F + k) + 1 from by ring]
    rw [show D + 1 = D + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show C + 2 * k + 2 = (C + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show C + 2 * k + 1 = (C + 2 * k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih A C (D + 1) (E + 2) F)
    rw [show D + 1 + k + 1 = D + (k + 1) + 1 from by ring,
        show E + 2 + 2 * k = E + 2 * (k + 1) from by ring]; finish

theorem r2r3_rounds : ∀ k, ∀ X B E,
    ⟨X, B, 0, k, E, 1⟩ [fm]⊢* ⟨X + k, B + k, 0, 0, E, 1⟩ := by
  intro k; induction' k with k ih <;> intro X B E
  · exists 0
  · rw [show k + 1 = k + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show B + 2 = (B + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (X + 1) (B + 1) E)
    rw [show X + 1 + k = X + (k + 1) from by ring,
        show B + 1 + k = B + (k + 1) from by ring]; finish

theorem main_trans (A F : ℕ) :
    ⟨A + 1, 0, 0, 0, 2 * F + 2, F + 1⟩ [fm]⊢⁺
    ⟨A + 2 * F + 3, 0, 0, 0, 2 * F + 4, F + 2⟩ := by
  have p1 : ⟨A + 1, 0, 0, 0, 2 * F + 2, F + 1⟩ [fm]⊢*
      ⟨A + 1, 0, 2 * F + 2, 0, 0, F + 1⟩ := by
    have := e_to_c (2 * F + 2) (A + 1) 0 (F + 1)
    simp only [Nat.zero_add] at this; exact this
  have p2 : ⟨A + 1, 0, 2 * F + 2, 0, 0, F + 1⟩ [fm]⊢⁺
      ⟨A, 1, 2 * F + 2, 0, 2, F + 1⟩ := by
    rw [show A + 1 = A + 1 from rfl]
    step fm; finish
  have p3 : ⟨A, 1, 2 * F + 2, 0, 2, F + 1⟩ [fm]⊢*
      ⟨A, 0, 2 * F + 1, 1, 3, F + 1⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show 2 * F + 2 = (2 * F + 1) + 1 from by ring]
    step fm; ring_nf; finish
  have p4 : ⟨A, 0, 2 * F + 1, 1, 3, F + 1⟩ [fm]⊢*
      ⟨A, 0, 1, F + 1, 2 * F + 3, 1⟩ := by
    have := r2r1r1_chain F A 1 0 3 1
    rw [show 1 + 2 * F = 2 * F + 1 from by ring,
        show 0 + 1 = 1 from by ring,
        show 0 + F + 1 = F + 1 from by ring,
        show 3 + 2 * F = 2 * F + 3 from by ring,
        show 1 + F = F + 1 from by ring] at this
    exact this
  have p5 : ⟨A, 0, 1, F + 1, 2 * F + 3, 1⟩ [fm]⊢*
      ⟨A, 1, 0, F + 1, 2 * F + 4, 0⟩ := by
    rw [show F + 1 = F + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    ring_nf; finish
  have p6 : ⟨A, 1, 0, F + 1, 2 * F + 4, 0⟩ [fm]⊢*
      ⟨A + 1, 0, 0, F + 1, 2 * F + 4, 1⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  have p7 : ⟨A + 1, 0, 0, F + 1, 2 * F + 4, 1⟩ [fm]⊢*
      ⟨A + F + 2, F + 1, 0, 0, 2 * F + 4, 1⟩ := by
    have := r2r3_rounds (F + 1) (A + 1) 0 (2 * F + 4)
    rw [show A + 1 + (F + 1) = A + F + 2 from by ring,
        show 0 + (F + 1) = F + 1 from by ring] at this
    exact this
  have p8 : ⟨A + F + 2, F + 1, 0, 0, 2 * F + 4, 1⟩ [fm]⊢*
      ⟨A + 2 * F + 3, 0, 0, 0, 2 * F + 4, F + 2⟩ := by
    have := r3_chain (F + 1) (A + F + 2) (2 * F + 4) 1
    rw [show A + F + 2 + (F + 1) = A + 2 * F + 3 from by ring,
        show 1 + (F + 1) = F + 2 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3
        (stepStar_trans p4
          (stepStar_trans p5
            (stepStar_trans p6
              (stepStar_trans p7 p8))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 2, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, F⟩ ↦ ⟨A + 1, 0, 0, 0, 2 * F + 2, F + 1⟩) ⟨0, 0⟩
  intro ⟨A, F⟩
  refine ⟨⟨A + 2 * F + 2, F + 1⟩, ?_⟩
  show ⟨A + 1, 0, 0, 0, 2 * F + 2, F + 1⟩ [fm]⊢⁺
    ⟨A + 2 * F + 2 + 1, 0, 0, 0, 2 * (F + 1) + 2, F + 1 + 1⟩
  rw [show A + 2 * F + 2 + 1 = A + 2 * F + 3 from by ring,
      show 2 * (F + 1) + 2 = 2 * F + 4 from by ring,
      show F + 1 + 1 = F + 2 from by ring]
  exact main_trans A F

end Sz22_2003_unofficial_1704
