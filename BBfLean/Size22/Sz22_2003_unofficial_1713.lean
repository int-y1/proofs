import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1713: [77/15, 99/14, 4/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  1
 2 -1  0  0  0
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1713

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) e)
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring]; finish

theorem r2_chain : ∀ k, ∀ A B E, ⟨A + k, B, 0, k, E⟩ [fm]⊢* ⟨A, B + 2 * k, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring, show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih A (B + 2) (E + 1))
    rw [show B + 2 + 2 * k = B + 2 * (k + 1) from by ring,
        show E + 1 + k = E + (k + 1) from by ring]; finish

theorem interleave : ∀ M, ∀ A D E,
    ⟨A + M, 0, 2 * M, D + 1, E⟩ [fm]⊢* ⟨A, 0, 0, D + M + 1, E + 3 * M⟩ := by
  intro M; induction' M with M ih <;> intro A D E
  · simp; exists 0
  · rw [show A + (M + 1) = (A + M) + 1 from by ring,
        show 2 * (M + 1) = 2 * M + 2 from by ring,
        show D + 1 = D + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih A (D + 1) (E + 3))
    rw [show D + 1 + M + 1 = D + (M + 1) + 1 from by ring,
        show E + 3 + 3 * M = E + 3 * (M + 1) from by ring]; finish

theorem main_trans (M : ℕ) :
    ⟨2 * M + 2, 0, 2 * M + 1, 0, 0⟩ [fm]⊢⁺ ⟨4 * M + 4, 0, 4 * M + 3, 0, 0⟩ := by
  have p1 : ⟨2 * M + 2, 0, 2 * M + 1, 0, 0⟩ [fm]⊢⁺
      ⟨2 * M + 1, 1, 2 * M + 1, 0, 1⟩ := by
    rw [show 2 * M + 2 = (2 * M + 1) + 1 from by ring]
    step fm; finish
  have p2 : ⟨2 * M + 1, 1, 2 * M + 1, 0, 1⟩ [fm]⊢⁺
      ⟨2 * M + 1, 0, 2 * M, 1, 2⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring, show 2 * M + 1 = (2 * M) + 1 from by ring]
    step fm; finish
  have p3 : ⟨2 * M + 1, 0, 2 * M, 1, 2⟩ [fm]⊢*
      ⟨M + 1, 0, 0, M + 1, 3 * M + 2⟩ := by
    rw [show 2 * M + 1 = (M + 1) + M from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    have h := interleave M (M + 1) 0 2
    rw [show 0 + M + 1 = M + 1 from by ring,
        show 2 + 3 * M = 3 * M + 2 from by ring] at h
    exact h
  have p4 : ⟨M + 1, 0, 0, M + 1, 3 * M + 2⟩ [fm]⊢*
      ⟨0, 2 * M + 2, 0, 0, 4 * M + 3⟩ := by
    have h := r2_chain (M + 1) 0 0 (3 * M + 2)
    rw [show 0 + 2 * (M + 1) = 2 * M + 2 from by ring,
        show 3 * M + 2 + (M + 1) = 4 * M + 3 from by ring] at h
    simp at h; exact h
  have p5 : ⟨0, 2 * M + 2, 0, 0, 4 * M + 3⟩ [fm]⊢*
      ⟨4 * M + 4, 0, 0, 0, 4 * M + 3⟩ := by
    have h := r3_chain (2 * M + 2) 0 (4 * M + 3)
    rw [show 0 + 2 * (2 * M + 2) = 4 * M + 4 from by ring] at h
    exact h
  have p6 : ⟨4 * M + 4, 0, 0, 0, 4 * M + 3⟩ [fm]⊢*
      ⟨4 * M + 4, 0, 4 * M + 3, 0, 0⟩ := by
    have h := r4_chain (4 * M + 3) (4 * M + 4) 0 0
    simp at h; exact h
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus
      (stepPlus_stepStar_stepPlus p1
        (stepStar_trans (stepPlus_stepStar p2) p3))
      p4)
    (stepStar_trans p5 p6)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun M ↦ ⟨2 * M + 2, 0, 2 * M + 1, 0, 0⟩) 0
  intro M
  refine ⟨2 * M + 1, ?_⟩
  show ⟨2 * M + 2, 0, 2 * M + 1, 0, 0⟩ [fm]⊢⁺
    ⟨2 * (2 * M + 1) + 2, 0, 2 * (2 * M + 1) + 1, 0, 0⟩
  rw [show 2 * (2 * M + 1) + 2 = 4 * M + 4 from by ring,
      show 2 * (2 * M + 1) + 1 = 4 * M + 3 from by ring]
  exact main_trans M

end Sz22_2003_unofficial_1713
