import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #484: [28/15, 3/22, 175/2, 11/7, 22/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  1  0
 0  0  0 -1  1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_484

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

theorem d_to_e : ∀ k c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · ring_nf; finish
  step fm; apply stepStar_trans (h _ _); ring_nf; finish

theorem a_to_c : ∀ k a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

theorem r2r1_chain : ∀ C, ∀ a D F,
    ⟨a + 1, 0, C, D, F + C⟩ [fm]⊢* ⟨a + C + 1, 0, 0, D + C, F⟩ := by
  intro C; induction' C with C h <;> intro a D F
  · ring_nf; finish
  rw [show F + (C + 1) = (F + C) + 1 from by ring]
  step fm; step fm
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans (h _ _ _); ring_nf; finish

theorem r2_drain : ∀ k a b d, ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm; apply stepStar_trans (h _ _ _); ring_nf; finish

theorem r3r1r1_rounds : ∀ k, ∀ a b d,
    ⟨a + 1, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, b, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show a + 4 = (a + 3) + 1 from by ring]
  apply stepStar_trans (h _ _ _); ring_nf; finish

theorem odd_tail (a d : ℕ) :
    ⟨a + 1, 1, 0, d, 0⟩ [fm]⊢* ⟨a + 2, 0, 1, d + 2, 0⟩ := by
  step fm; step fm; finish

theorem trans_even (a₀ k : ℕ) (ha : a₀ ≥ 1) :
    ⟨0, 0, a₀ + 2 * k + 2, a₀ + 4 * k + 2, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2 * a₀ + 6 * k + 6, 2 * a₀ + 8 * k + 7, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_e (a₀ + 4 * k + 2) (a₀ + 2 * k + 2) 0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, a₀ + 2 * k + 2, 0, 0 + (a₀ + 4 * k + 2)⟩ =
        some ⟨1, 0, a₀ + 2 * k + 1, 0, 0 + (a₀ + 4 * k + 2) + 1⟩
    simp [fm]
  apply stepStar_trans
  · have h := r2r1_chain (a₀ + 2 * k + 1) 0 0 (2 * k + 2)
    rw [show 0 + 1 = 1 from rfl,
        show (2 * k + 2) + (a₀ + 2 * k + 1) = 0 + (a₀ + 4 * k + 2) + 1 from by ring,
        show 0 + (a₀ + 2 * k + 1) + 1 = a₀ + 2 * k + 2 from by ring,
        show 0 + (a₀ + 2 * k + 1) = a₀ + 2 * k + 1 from by ring] at h
    exact h
  apply stepStar_trans
  · have h := r2_drain (2 * k + 2) a₀ 0 (a₀ + 2 * k + 1)
    rw [show a₀ + (2 * k + 2) = a₀ + 2 * k + 2 from by ring,
        show 0 + (2 * k + 2) = 2 * k + 2 from by ring] at h
    exact h
  apply stepStar_trans
  · have h := r3r1r1_rounds (k + 1) (a₀ - 1) 0 (a₀ + 2 * k + 1)
    rw [show a₀ - 1 + 1 = a₀ from by omega,
        show 0 + 2 * (k + 1) = 2 * k + 2 from by ring,
        show a₀ - 1 + 3 * (k + 1) + 1 = a₀ + 3 * k + 3 from by omega,
        show a₀ + 2 * k + 1 + 3 * (k + 1) = a₀ + 5 * k + 4 from by ring] at h
    exact h
  have h := a_to_c (a₀ + 3 * k + 3) 0 0 (a₀ + 5 * k + 4)
  rw [show 0 + (a₀ + 3 * k + 3) = a₀ + 3 * k + 3 from by ring,
      show 0 + 2 * (a₀ + 3 * k + 3) = 2 * a₀ + 6 * k + 6 from by ring,
      show a₀ + 5 * k + 4 + (a₀ + 3 * k + 3) = 2 * a₀ + 8 * k + 7 from by ring] at h
  exact h

theorem trans_odd (a₁ j : ℕ) (ha : a₁ ≥ 1) :
    ⟨0, 0, a₁ + 2 * j + 3, a₁ + 4 * j + 4, 0⟩ [fm]⊢⁺
    ⟨0, 0, 2 * a₁ + 6 * j + 9, 2 * a₁ + 8 * j + 11, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_e (a₁ + 4 * j + 4) (a₁ + 2 * j + 3) 0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, a₁ + 2 * j + 3, 0, 0 + (a₁ + 4 * j + 4)⟩ =
        some ⟨1, 0, a₁ + 2 * j + 2, 0, 0 + (a₁ + 4 * j + 4) + 1⟩
    simp [fm]
  apply stepStar_trans
  · have h := r2r1_chain (a₁ + 2 * j + 2) 0 0 (2 * j + 3)
    rw [show 0 + 1 = 1 from rfl,
        show (2 * j + 3) + (a₁ + 2 * j + 2) = 0 + (a₁ + 4 * j + 4) + 1 from by ring,
        show 0 + (a₁ + 2 * j + 2) + 1 = a₁ + 2 * j + 3 from by ring,
        show 0 + (a₁ + 2 * j + 2) = a₁ + 2 * j + 2 from by ring] at h
    exact h
  apply stepStar_trans
  · have h := r2_drain (2 * j + 3) a₁ 0 (a₁ + 2 * j + 2)
    rw [show a₁ + (2 * j + 3) = a₁ + 2 * j + 3 from by ring,
        show 0 + (2 * j + 3) = 2 * j + 3 from by ring] at h
    exact h
  apply stepStar_trans
  · have h := r3r1r1_rounds (j + 1) (a₁ - 1) 1 (a₁ + 2 * j + 2)
    rw [show a₁ - 1 + 1 = a₁ from by omega,
        show 1 + 2 * (j + 1) = 2 * j + 3 from by ring,
        show a₁ - 1 + 3 * (j + 1) + 1 = a₁ + 3 * j + 3 from by omega,
        show a₁ + 2 * j + 2 + 3 * (j + 1) = a₁ + 5 * j + 5 from by ring] at h
    exact h
  apply stepStar_trans (odd_tail (a₁ + 3 * j + 2) (a₁ + 5 * j + 5))
  have h := a_to_c (a₁ + 3 * j + 4) 0 1 (a₁ + 5 * j + 7)
  rw [show 0 + (a₁ + 3 * j + 4) = a₁ + 3 * j + 4 from by ring,
      show 1 + 2 * (a₁ + 3 * j + 4) = 2 * a₁ + 6 * j + 9 from by ring,
      show a₁ + 5 * j + 7 + (a₁ + 3 * j + 4) = 2 * a₁ + 8 * j + 11 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 5, 0⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ C n, q = (⟨0, 0, C, C + n, 0⟩ : Q) ∧ C ≥ n + 3)
  · intro q ⟨C, n, hq, hC⟩; subst hq
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- Even n = k + k
      subst hk
      obtain ⟨a₀, rfl⟩ : ∃ a₀, C = a₀ + 2 * k + 2 := ⟨C - 2 * k - 2, by omega⟩
      refine ⟨⟨0, 0, 2 * a₀ + 6 * k + 6, (2 * a₀ + 6 * k + 6) + (2 * k + 1), 0⟩,
              ⟨2 * a₀ + 6 * k + 6, 2 * k + 1, ?_, ?_⟩, ?_⟩
      · rfl
      · omega
      · have h := trans_even a₀ k (by omega)
        rw [show a₀ + 4 * k + 2 = a₀ + 2 * k + 2 + (k + k) from by ring,
            show 2 * a₀ + 8 * k + 7 = 2 * a₀ + 6 * k + 6 + (2 * k + 1) from by ring] at h
        exact h
    · -- Odd n = 2 * k + 1
      subst hk
      obtain ⟨a₁, rfl⟩ : ∃ a₁, C = a₁ + 2 * k + 3 := ⟨C - 2 * k - 3, by omega⟩
      refine ⟨⟨0, 0, 2 * a₁ + 6 * k + 9, (2 * a₁ + 6 * k + 9) + (2 * k + 2), 0⟩,
              ⟨2 * a₁ + 6 * k + 9, 2 * k + 2, ?_, ?_⟩, ?_⟩
      · rfl
      · omega
      · have h := trans_odd a₁ k (by omega)
        rw [show a₁ + 4 * k + 4 = a₁ + 2 * k + 3 + (2 * k + 1) from by ring,
            show 2 * a₁ + 8 * k + 11 = 2 * a₁ + 6 * k + 9 + (2 * k + 2) from by ring] at h
        exact h
  · exact ⟨5, 0, rfl, by omega⟩

end Sz22_2003_unofficial_484
