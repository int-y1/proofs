import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #645: [35/6, 143/2, 52/55, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  1
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_645

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

theorem d_to_b : ∀ k, ∀ b E F, ⟨0, b, 0, k, E, F⟩ [fm]⊢* ⟨0, b + k, 0, 0, E, F⟩ := by
  intro k; induction' k with k ih <;> intro b E F
  · simp; exists 0
  rw [show b + (k + 1) = (b + 1) + k from by ring]; step fm; exact ih _ _ _

theorem r1r1r3_chain : ∀ k, ∀ b C D E F,
    ⟨2, b + 2 * k, C, D, E + k, F⟩ [fm]⊢* ⟨2, b, C + k, D + 2 * k, E, F + k⟩ := by
  intro k; induction' k with k ih <;> intro b C D E F
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm
  rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _ _ _); ring_nf; finish

theorem b1_drain : ∀ C D E F,
    ⟨2, 1, C, D, E, F⟩ [fm]⊢* ⟨2, 0, C, D + 1, E, F + 2⟩ := by
  intro C D E F; step fm; step fm; step fm; finish

theorem r2r2r3_chain : ∀ k, ∀ D E F,
    ⟨2, 0, k, D, E, F⟩ [fm]⊢* ⟨2, 0, 0, D, E + k, F + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro D E F
  · exists 0
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem final_r2r2 : ∀ D E F, ⟨2, 0, 0, D, E, F⟩ [fm]⊢* ⟨0, 0, 0, D, E + 2, F + 2⟩ := by
  intro D E F; step fm; step fm; finish

theorem even_trans (m : ℕ) :
    (⟨0, 0, 0, 2 * m + 1, 2 * m + 2, 4 * m * m + 2 * m + 1⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 2, 2 * m + 3, 4 * m * m + 6 * m + 3⟩ := by
  have hd := d_to_b (2 * m + 1) 0 (2 * m + 2) (4 * m * m + 2 * m + 1)
  simp only [Nat.zero_add] at hd
  apply stepStar_stepPlus_stepPlus hd
  step fm; step fm; step fm
  -- State: (2, 2*m, 0, 2, 2*m+1, 4*m*m+2*m+1)
  apply stepStar_trans (c₂ := ⟨2, 0, m, 2 * m + 2, m + 1, 4 * m * m + 3 * m + 1⟩)
  · have h := r1r1r3_chain m 0 0 2 (m + 1) (4 * m * m + 2 * m + 1)
    simp only [Nat.zero_add, (by ring : 2 + 2 * m = 2 * m + 2),
               (by ring : 4 * m * m + 2 * m + 1 + m = 4 * m * m + 3 * m + 1)] at h
    convert h using 2; all_goals ring_nf
  apply stepStar_trans (r2r2r3_chain m (2 * m + 2) (m + 1) (4 * m * m + 3 * m + 1))
  apply stepStar_trans (final_r2r2 (2 * m + 2) _ _)
  ring_nf; finish

theorem odd_trans (m : ℕ) :
    (⟨0, 0, 0, 2 * m + 2, 2 * m + 3, 4 * m * m + 6 * m + 3⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 3, 2 * m + 4, 4 * m * m + 10 * m + 7⟩ := by
  have hd := d_to_b (2 * m + 2) 0 (2 * m + 3) (4 * m * m + 6 * m + 3)
  simp only [Nat.zero_add] at hd
  apply stepStar_stepPlus_stepPlus hd
  step fm; step fm; step fm
  rw [show 2 * m + 1 = 1 + 2 * m from by ring,
      show 2 * m + 2 = (m + 2) + m from by ring]
  apply stepStar_trans (r1r1r3_chain m 1 0 2 (m + 2) (4 * m * m + 6 * m + 3))
  rw [show (0 : ℕ) + m = m from by ring, show 2 + 2 * m = 2 * m + 2 from by ring,
      show 4 * m * m + 6 * m + 3 + m = 4 * m * m + 7 * m + 3 from by ring]
  apply stepStar_trans (b1_drain m (2 * m + 2) (m + 2) (4 * m * m + 7 * m + 3))
  rw [show 2 * m + 2 + 1 = 2 * m + 3 from by ring,
      show 4 * m * m + 7 * m + 3 + 2 = 4 * m * m + 7 * m + 5 from by ring]
  apply stepStar_trans (r2r2r3_chain m (2 * m + 3) (m + 2) (4 * m * m + 7 * m + 5))
  apply stepStar_trans (final_r2r2 (2 * m + 3) _ _)
  ring_nf; finish

theorem main_trans (n : ℕ) : (⟨0, 0, 0, n + 1, n + 2, n * n + n + 1⟩ : Q) [fm]⊢⁺
    ⟨0, 0, 0, n + 2, n + 3, n * n + 3 * n + 3⟩ := by
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
  · subst hK
    rw [show K + K + 1 = 2 * K + 1 from by ring,
        show K + K + 2 = 2 * K + 2 from by ring,
        show K + K + 3 = 2 * K + 3 from by ring,
        show (K + K) * (K + K) + (K + K) + 1 = 4 * K * K + 2 * K + 1 from by ring,
        show (K + K) * (K + K) + 3 * (K + K) + 3 = 4 * K * K + 6 * K + 3 from by ring]
    exact even_trans K
  · subst hK
    rw [show 2 * K + 1 + 1 = 2 * K + 2 from by ring,
        show 2 * K + 1 + 2 = 2 * K + 3 from by ring,
        show 2 * K + 1 + 3 = 2 * K + 4 from by ring,
        show (2 * K + 1) * (2 * K + 1) + (2 * K + 1) + 1 = 4 * K * K + 6 * K + 3 from by ring,
        show (2 * K + 1) * (2 * K + 1) + 3 * (2 * K + 1) + 3 = 4 * K * K + 10 * K + 7 from by ring]
    exact odd_trans K

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 1, n + 2, n * n + n + 1⟩) 0
  intro n
  have h := main_trans n
  rw [show n * n + 3 * n + 3 = (n + 1) * (n + 1) + (n + 1) + 1 from by ring] at h
  exact ⟨n + 1, h⟩

end Sz22_2003_unofficial_645
