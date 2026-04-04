import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1644: [77/15, 27/14, 44/3, 5/11, 3/2]

Vector representation:
```
 0 -1 -1  1  1
-1  3  0 -1  0
 2 -1  0  0  1
 0  0  1  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1644

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1)); ring_nf; finish

theorem r3_chain : ∀ k, ∀ A E, ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · step fm; apply stepStar_trans (ih (A + 2) (E + 1)); ring_nf; finish

theorem r2_chain : ∀ k, ∀ A B E, ⟨A + k, B, 0, k, E⟩ [fm]⊢* ⟨A, B + 3 * k, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih A (B + 3) E); ring_nf; finish

theorem interleaved : ∀ K, ∀ A D E,
    ⟨A + K, 0, 3 * K, D + 1, E⟩ [fm]⊢* ⟨A, 0, 0, D + 2 * K + 1, E + 3 * K⟩ := by
  intro K; induction' K with K ih <;> intro A D E
  · simp; exists 0
  · rw [show A + (K + 1) = (A + K) + 1 from by ring,
        show 3 * (K + 1) = 3 * K + 3 from by ring]
    step fm
    rw [show (3 * K + 3 : ℕ) = (3 * K + 2) + 1 from by ring]
    step fm
    rw [show (3 * K + 2 : ℕ) = (3 * K + 1) + 1 from by ring]
    step fm
    rw [show (3 * K + 1 : ℕ) = (3 * K) + 1 from by ring]
    step fm
    rw [show (D + 3 : ℕ) = (D + 2) + 1 from by ring]
    apply stepStar_trans (ih A (D + 2) (E + 3))
    rw [show D + 2 + 2 * K + 1 = D + 2 * (K + 1) + 1 from by ring,
        show E + 3 + 3 * K = E + 3 * (K + 1) from by ring]
    finish

theorem main_trans (K F : ℕ) :
    ⟨3 * K + F + 2, 0, 3 * K + 1, 0, 0⟩ [fm]⊢⁺
    ⟨12 * K + F + 6, 0, 9 * K + 4, 0, 0⟩ := by
  have p1 : ⟨3 * K + F + 2, 0, 3 * K + 1, 0, 0⟩ [fm]⊢*
      ⟨3 * K + F + 1, 1, 3 * K + 1, 0, 0⟩ := by
    rw [show 3 * K + F + 2 = (3 * K + F + 1) + 1 from by ring]
    step fm; finish
  have p2 : ⟨3 * K + F + 1, 1, 3 * K + 1, 0, 0⟩ [fm]⊢*
      ⟨3 * K + F + 1, 0, 3 * K, 1, 1⟩ := by
    rw [show (3 * K + 1 : ℕ) = (3 * K) + 1 from by ring]
    step fm; finish
  have p3 : ⟨3 * K + F + 1, 0, 3 * K, 1, 1⟩ [fm]⊢*
      ⟨2 * K + F + 1, 0, 0, 2 * K + 1, 3 * K + 1⟩ := by
    rw [show 3 * K + F + 1 = (2 * K + F + 1) + K from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (interleaved K (2 * K + F + 1) 0 1)
    ring_nf; finish
  have p4 : ⟨2 * K + F + 1, 0, 0, 2 * K + 1, 3 * K + 1⟩ [fm]⊢*
      ⟨F, 6 * K + 3, 0, 0, 3 * K + 1⟩ := by
    rw [show 2 * K + F + 1 = F + (2 * K + 1) from by ring]
    apply stepStar_trans (r2_chain (2 * K + 1) F 0 (3 * K + 1))
    ring_nf; finish
  have p5 : ⟨F, 6 * K + 3, 0, 0, 3 * K + 1⟩ [fm]⊢*
      ⟨12 * K + F + 6, 0, 0, 0, 9 * K + 4⟩ := by
    apply stepStar_trans (r3_chain (6 * K + 3) F (3 * K + 1))
    ring_nf; finish
  have p6 : ⟨12 * K + F + 6, 0, 0, 0, 9 * K + 4⟩ [fm]⊢*
      ⟨12 * K + F + 6, 0, 9 * K + 4, 0, 0⟩ := by
    have := e_to_c (a := 12 * K + F + 6) (9 * K + 4) 0
    simpa using this
  exact stepStar_stepPlus
    (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4
      (stepStar_trans p5 p6)))))
    (by simp [Q]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨K, F⟩ ↦ ⟨3 * K + F + 2, 0, 3 * K + 1, 0, 0⟩) ⟨0, 0⟩
  intro ⟨K, F⟩
  refine ⟨⟨3 * K + 1, 3 * K + F + 1⟩, ?_⟩
  show ⟨3 * K + F + 2, 0, 3 * K + 1, 0, 0⟩ [fm]⊢⁺
    ⟨3 * (3 * K + 1) + (3 * K + F + 1) + 2, 0, 3 * (3 * K + 1) + 1, 0, 0⟩
  rw [show 3 * (3 * K + 1) + (3 * K + F + 1) + 2 = 12 * K + F + 6 from by ring,
      show 3 * (3 * K + 1) + 1 = 9 * K + 4 from by ring]
  exact main_trans K F

end Sz22_2003_unofficial_1644
