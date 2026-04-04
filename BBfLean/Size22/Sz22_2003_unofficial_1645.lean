import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1645: [77/15, 27/91, 26/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1  0
 0  3  0 -1  0 -1
 1 -1  0  0  0  1
 0  0  1  0 -1  0
-1  1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1645

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+3, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

theorem r4_chain : ∀ k a c e fv, ⟨a, 0, c, 0, e + k, fv⟩ [fm]⊢* ⟨a, 0, c + k, 0, e, fv⟩ := by
  intro k; induction' k with k ih <;> intro a c e fv
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e fv)
    ring_nf; finish

theorem r3_chain : ∀ k a e f, ⟨a, k, 0, 0, e, f⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) e (f + 1))
    ring_nf; finish

theorem interleave : ∀ M, ∀ A B C D E F,
    2 * C + D = M →
    ⟨A, B + 1, C, D, E, F + C + D⟩ [fm]⊢* ⟨A, B + 2 * C + 3 * D + 1, 0, 0, E + C, F⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B C D E F hM
  rcases C with _ | C
  · rcases D with _ | D
    · simp; exists 0
    · show ⟨A, B + 1, 0, D + 1, E, F + 0 + (D + 1)⟩ [fm]⊢*
        ⟨A, B + 2 * 0 + 3 * (D + 1) + 1, 0, 0, E + 0, F⟩
      rw [show F + 0 + (D + 1) = (F + D) + 1 from by ring, show D + 1 = D + 1 from rfl]
      step fm
      rw [show B + 4 = (B + 3) + 1 from by ring]
      have h := ih (2 * 0 + D) (by omega) A (B + 3) 0 D E F (by ring)
      rw [show F + 0 + D = F + D from by ring,
          show B + 3 + 2 * 0 + 3 * D + 1 = B + 2 * 0 + 3 * (D + 1) + 1 from by ring,
          show E + 0 = E + 0 from rfl] at h
      exact h
  · rcases B with _ | B
    · show ⟨A, 0 + 1, C + 1, D, E, F + (C + 1) + D⟩ [fm]⊢*
        ⟨A, 0 + 2 * (C + 1) + 3 * D + 1, 0, 0, E + (C + 1), F⟩
      rw [show F + (C + 1) + D = (F + C + D) + 1 from by ring, show C + 1 = C + 1 from rfl]
      step fm
      rw [show D + 1 = D + 1 from rfl, show F + C + D + 1 = (F + C + D) + 1 from by ring]
      step fm
      rw [show (3 : ℕ) = 2 + 1 from by ring]
      have h := ih (2 * C + D) (by omega) A 2 C D (E + 1) F (by ring)
      rw [show F + C + D = F + C + D from rfl,
          show 2 + 2 * C + 3 * D + 1 = 0 + 2 * (C + 1) + 3 * D + 1 from by ring,
          show E + 1 + C = E + (C + 1) from by ring] at h
      exact h
    · show ⟨A, B + 1 + 1, C + 1, D, E, F + (C + 1) + D⟩ [fm]⊢*
        ⟨A, B + 1 + 2 * (C + 1) + 3 * D + 1, 0, 0, E + (C + 1), F⟩
      rw [show B + 1 + 1 = (B + 1) + 1 from by ring,
          show F + (C + 1) + D = (F + C + D) + 1 from by ring,
          show C + 1 = C + 1 from rfl]
      step fm
      have h := ih (2 * C + (D + 1)) (by omega) A B C (D + 1) (E + 1) F (by ring)
      rw [show F + C + (D + 1) = F + C + D + 1 from by ring,
          show B + 2 * C + 3 * (D + 1) + 1 = B + 1 + 2 * (C + 1) + 3 * D + 1 from by ring,
          show E + 1 + C = E + (C + 1) from by ring] at h
      exact h

theorem main_trans (a e f : ℕ) :
    ⟨a + 1, 0, 0, 0, e + 1, f + e + 1⟩ [fm]⊢⁺ ⟨a + 2 * e + 3, 0, 0, 0, e + 2, f + 2 * e + 3⟩ := by
  have phase1 : ⟨a + 1, 0, 0, 0, e + 1, f + e + 1⟩ [fm]⊢* ⟨a + 1, 0, e + 1, 0, 0, f + e + 1⟩ := by
    have := r4_chain (e + 1) (a + 1) 0 0 (f + e + 1); simp at this; exact this
  have phase2 : ⟨a + 1, 0, e + 1, 0, 0, f + e + 1⟩ [fm]⊢⁺ ⟨a, 1, e + 1, 0, 1, f + e + 1⟩ := by
    rw [show e + 1 = 0 + (e + 1) from by ring]; step fm; finish
  have phase3 : ⟨a, 1, e + 1, 0, 1, f + e + 1⟩ [fm]⊢* ⟨a, 2 * e + 3, 0, 0, e + 2, f⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    have h := interleave (2 * (e + 1) + 0) a 0 (e + 1) 0 1 f (by ring)
    rw [show f + (e + 1) + 0 = f + e + 1 from by ring,
        show 0 + 2 * (e + 1) + 3 * 0 + 1 = 2 * e + 3 from by ring,
        show 1 + (e + 1) = e + 2 from by ring] at h
    exact h
  have phase4 : ⟨a, 2 * e + 3, 0, 0, e + 2, f⟩ [fm]⊢* ⟨a + (2 * e + 3), 0, 0, 0, e + 2, f + (2 * e + 3)⟩ :=
    r3_chain (2 * e + 3) a (e + 2) f
  have phase34 : ⟨a, 1, e + 1, 0, 1, f + e + 1⟩ [fm]⊢* ⟨a + 2 * e + 3, 0, 0, 0, e + 2, f + 2 * e + 3⟩ := by
    apply stepStar_trans phase3
    rw [show a + (2 * e + 3) = a + 2 * e + 3 from by ring,
        show f + (2 * e + 3) = f + 2 * e + 3 from by ring] at phase4
    exact phase4
  exact stepStar_stepPlus_stepPlus phase1 (stepPlus_stepStar_stepPlus phase2 phase34)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1, 1⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 1, 0, 0, 0, p.2.1 + 1, p.2.2 + p.2.1 + 1⟩) ⟨0, 0, 0⟩
  intro ⟨a, e, f⟩
  refine ⟨⟨a + 2 * e + 2, e + 1, f + e + 1⟩, ?_⟩
  show ⟨a + 1, 0, 0, 0, e + 1, f + e + 1⟩ [fm]⊢⁺ ⟨a + 2 * e + 2 + 1, 0, 0, 0, e + 1 + 1, f + e + 1 + (e + 1) + 1⟩
  rw [show a + 2 * e + 2 + 1 = a + 2 * e + 3 from by ring,
      show e + 1 + 1 = e + 2 from by ring,
      show f + e + 1 + (e + 1) + 1 = f + 2 * e + 3 from by ring]
  exact main_trans a e f
