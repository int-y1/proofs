import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1691: [77/15, 9/14, 44/3, 5/11, 9/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 2 -1  0  0  1
 0  0  1  0 -1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1691

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1))
    rw [show C + 1 + k = C + (k + 1) from by ring]; finish

theorem r2_chain : ∀ k, ∀ A B E,
    ⟨A + k, B, 0, k, E⟩ [fm]⊢* ⟨A, B + 2 * k, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih A (B + 2) E)
    rw [show B + 2 + 2 * k = B + 2 * (k + 1) from by ring]; finish

theorem r3_chain : ∀ k, ∀ A E,
    ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (A + 2) (E + 1))
    rw [show A + 2 + 2 * k = A + 2 * (k + 1) from by ring,
        show E + 1 + k = E + (k + 1) from by ring]; finish

theorem r2r1r1_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C + 2 * k, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + 1 + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A C (D + 1) (E + 2))
    rw [show D + 1 + 1 + k = D + 1 + (k + 1) from by ring,
        show E + 2 + 2 * k = E + 2 * (k + 1) from by ring]; finish

theorem main_trans (n F : ℕ) :
    ⟨2 * n + F + 4, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺
    ⟨4 * n + F + 9, 0, 0, 0, 4 * n + 6⟩ := by
  have p1 : ⟨2 * n + F + 4, 0, 0, 0, 2 * n + 2⟩ [fm]⊢*
      ⟨2 * n + F + 4, 0, 2 * n + 2, 0, 0⟩ := by
    have := r4_chain (2 * n + 2) (2 * n + F + 4) 0
    simp only [Nat.zero_add] at this; exact this
  have p2 : ⟨2 * n + F + 4, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺
      ⟨2 * n + F + 3, 2, 2 * n + 2, 0, 0⟩ := by
    rw [show 2 * n + F + 4 = (2 * n + F + 3) + 1 from by ring]
    step fm; finish
  have p3 : ⟨2 * n + F + 3, 2, 2 * n + 2, 0, 0⟩ [fm]⊢*
      ⟨2 * n + F + 3, 0, 2 * n, 2, 2⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl, show 2 * n + 1 = (2 * n) + 1 from by ring]
    step fm; ring_nf; finish
  have p4 : ⟨2 * n + F + 3, 0, 2 * n, 2, 2⟩ [fm]⊢*
      ⟨F + n + 3, 0, 0, n + 2, 2 * n + 2⟩ := by
    have := r2r1r1_chain n (F + n + 3) 0 1 2
    rw [show F + n + 3 + n = 2 * n + F + 3 from by ring,
        show 0 + 2 * n = 2 * n from by ring,
        show 1 + 1 + n = n + 2 from by ring,
        show 2 + 2 * n = 2 * n + 2 from by ring] at this
    exact this
  have p5 : ⟨F + n + 3, 0, 0, n + 2, 2 * n + 2⟩ [fm]⊢*
      ⟨F + 1, 2 * n + 4, 0, 0, 2 * n + 2⟩ := by
    rw [show F + n + 3 = (F + 1) + (n + 2) from by ring]
    have := r2_chain (n + 2) (F + 1) 0 (2 * n + 2)
    rw [show 0 + 2 * (n + 2) = 2 * n + 4 from by ring] at this
    exact this
  have p6 : ⟨F + 1, 2 * n + 4, 0, 0, 2 * n + 2⟩ [fm]⊢*
      ⟨4 * n + F + 9, 0, 0, 0, 4 * n + 6⟩ := by
    have := r3_chain (2 * n + 4) (F + 1) (2 * n + 2)
    rw [show F + 1 + 2 * (2 * n + 4) = 4 * n + F + 9 from by ring,
        show 2 * n + 2 + (2 * n + 4) = 4 * n + 6 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 p6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 2⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, F⟩ ↦ ⟨2 * n + F + 4, 0, 0, 0, 2 * n + 2⟩) ⟨0, 0⟩
  intro ⟨n, F⟩
  refine ⟨⟨2 * n + 2, F + 1⟩, ?_⟩
  show ⟨2 * n + F + 4, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺
    ⟨2 * (2 * n + 2) + (F + 1) + 4, 0, 0, 0, 2 * (2 * n + 2) + 2⟩
  rw [show 2 * (2 * n + 2) + (F + 1) + 4 = 4 * n + F + 9 from by ring,
      show 2 * (2 * n + 2) + 2 = 4 * n + 6 from by ring]
  exact main_trans n F

end Sz22_2003_unofficial_1691
