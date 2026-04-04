import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1611: [77/15, 2/3, 27/14, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  0  0
-1  3  0 -1  0
 0  0  1  0 -1
-1  1  0  1  1
```

This Fractran program doesn't halt.

Canonical states: (A+c+3, 0, c+1, 0, 0) with quadratic growth in A.
Transition: (A+c+3, 0, c+1, 0, 0) -> (A+2c+6, 0, c+2, 0, 0), mapping (A,c) -> (A+c+2, c+1).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1611

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C, ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm; apply stepStar_trans (ih A (C + 1)); ring_nf; finish

theorem r3r2_drain : ∀ k, ∀ A E, ⟨A + 1, 0, 0, k, E⟩ [fm]⊢* ⟨A + 2 * k + 1, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · simp; exists 0
  · step fm; step fm; step fm; step fm
    rw [show A + 2 * (k + 1) + 1 = (A + 2) + 2 * k + 1 from by ring]
    exact ih (A + 2) E

theorem opening_round : ∀ A C D E,
    ⟨A + 1, 0, C + 3, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + 3, E + 3⟩ := by
  intro A C D E
  apply stepStar_trans (c₂ := ⟨A, 3, C + 3, D, E⟩)
  · step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 2, C + 2, D + 1, E + 1⟩)
  · rw [show C + 3 = (C + 2) + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
    step fm; finish
  apply stepStar_trans (c₂ := ⟨A, 1, C + 1, D + 2, E + 2⟩)
  · rw [show C + 2 = (C + 1) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    step fm; finish
  rw [show C + 1 = C + 1 from rfl, show (1 : ℕ) = 0 + 1 from by ring]
  step fm; ring_nf; finish

theorem opening_rounds : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C + 3 * k, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + 2 * k + 1, E + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 3 * (k + 1) = (C + 3 * k) + 3 from by ring]
    apply stepStar_trans (opening_round (A + k) (C + 3 * k) D E)
    rw [show D + 3 = (D + 2) + 1 from by ring]
    apply stepStar_trans (ih A C (D + 2) (E + 3))
    ring_nf; finish

theorem tail_c1 : ∀ A D E,
    ⟨A + 1, 0, 1, D + 1, E⟩ [fm]⊢* ⟨A + 2, 0, 0, D + 1, E + 1⟩ := by
  intro A D E
  step fm; step fm; step fm; step fm; ring_nf; finish

theorem tail_c2 : ∀ A D E,
    ⟨A + 1, 0, 2, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + 2, E + 2⟩ := by
  intro A D E
  apply stepStar_trans (c₂ := ⟨A, 3, 2, D, E⟩)
  · step fm; finish
  rw [show (2 : ℕ) = 1 + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  step fm
  rw [show D + 1 + 1 = D + 2 from by ring, show E + 1 + 1 = E + 2 from by ring]
  step fm; ring_nf; finish

theorem trans_mod0 (j A : ℕ) :
    ⟨A + 3 * j + 3, 0, 3 * j + 1, 0, 0⟩ [fm]⊢⁺
    ⟨A + 6 * j + 6, 0, 3 * j + 2, 0, 0⟩ := by
  have p1 : ⟨A + 3 * j + 3, 0, 3 * j + 1, 0, 0⟩ [fm]⊢*
      ⟨A + 3 * j + 2, 0, 3 * j, 2, 2⟩ := by
    rw [show A + 3 * j + 3 = (A + 3 * j + 2) + 1 from by ring,
        show 3 * j + 1 = (3 * j) + 1 from by ring]
    step fm; step fm; finish
  have p2 : ⟨A + 3 * j + 2, 0, 3 * j, 2, 2⟩ [fm]⊢*
      ⟨A + 2 * j + 2, 0, 0, 2 * j + 2, 3 * j + 2⟩ := by
    have h := opening_rounds j (A + 2 * j + 2) 0 1 2
    rw [show (A + 2 * j + 2) + j = A + 3 * j + 2 from by ring,
        show 0 + 3 * j = 3 * j from by ring,
        show 1 + 2 * j + 1 = 2 * j + 2 from by ring,
        show 2 + 3 * j = 3 * j + 2 from by ring,
        show (1 + 1 : ℕ) = 2 from by ring] at h
    exact h
  have p3 : ⟨A + 2 * j + 2, 0, 0, 2 * j + 2, 3 * j + 2⟩ [fm]⊢*
      ⟨A + 6 * j + 6, 0, 0, 0, 3 * j + 2⟩ := by
    rw [show A + 2 * j + 2 = (A + 2 * j + 1) + 1 from by ring]
    have h := r3r2_drain (2 * j + 2) (A + 2 * j + 1) (3 * j + 2)
    rw [show A + 2 * j + 1 + 2 * (2 * j + 2) + 1 = A + 6 * j + 6 from by ring] at h
    exact h
  have p4 : ⟨A + 6 * j + 6, 0, 0, 0, 3 * j + 2⟩ [fm]⊢*
      ⟨A + 6 * j + 6, 0, 3 * j + 2, 0, 0⟩ := by
    have h := e_to_c (3 * j + 2) (A + 6 * j + 6) 0
    simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3 p4)))
    (by simp [Q])

theorem trans_mod1 (j A : ℕ) :
    ⟨A + 3 * j + 4, 0, 3 * j + 2, 0, 0⟩ [fm]⊢⁺
    ⟨A + 6 * j + 8, 0, 3 * j + 3, 0, 0⟩ := by
  have p1 : ⟨A + 3 * j + 4, 0, 3 * j + 2, 0, 0⟩ [fm]⊢*
      ⟨A + 3 * j + 3, 0, 3 * j + 1, 2, 2⟩ := by
    rw [show A + 3 * j + 4 = (A + 3 * j + 3) + 1 from by ring,
        show 3 * j + 2 = (3 * j + 1) + 1 from by ring]
    step fm; step fm; finish
  have p2 : ⟨A + 3 * j + 3, 0, 3 * j + 1, 2, 2⟩ [fm]⊢*
      ⟨A + 2 * j + 3, 0, 1, 2 * j + 2, 3 * j + 2⟩ := by
    have h := opening_rounds j (A + 2 * j + 3) 1 1 2
    rw [show (A + 2 * j + 3) + j = A + 3 * j + 3 from by ring,
        show 1 + 3 * j = 3 * j + 1 from by ring,
        show 1 + 2 * j + 1 = 2 * j + 2 from by ring,
        show 2 + 3 * j = 3 * j + 2 from by ring,
        show (1 + 1 : ℕ) = 2 from by ring] at h
    exact h
  have p3 : ⟨A + 2 * j + 3, 0, 1, 2 * j + 2, 3 * j + 2⟩ [fm]⊢*
      ⟨A + 2 * j + 4, 0, 0, 2 * j + 2, 3 * j + 3⟩ := by
    rw [show A + 2 * j + 3 = (A + 2 * j + 2) + 1 from by ring,
        show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
    have h := tail_c1 (A + 2 * j + 2) (2 * j + 1) (3 * j + 2)
    rw [show A + 2 * j + 2 + 2 = A + 2 * j + 4 from by ring,
        show 2 * j + 1 + 1 = 2 * j + 2 from by ring] at h
    exact h
  have p4 : ⟨A + 2 * j + 4, 0, 0, 2 * j + 2, 3 * j + 3⟩ [fm]⊢*
      ⟨A + 6 * j + 8, 0, 0, 0, 3 * j + 3⟩ := by
    rw [show A + 2 * j + 4 = (A + 2 * j + 3) + 1 from by ring]
    have h := r3r2_drain (2 * j + 2) (A + 2 * j + 3) (3 * j + 3)
    rw [show A + 2 * j + 3 + 2 * (2 * j + 2) + 1 = A + 6 * j + 8 from by ring] at h
    exact h
  have p5 : ⟨A + 6 * j + 8, 0, 0, 0, 3 * j + 3⟩ [fm]⊢*
      ⟨A + 6 * j + 8, 0, 3 * j + 3, 0, 0⟩ := by
    have h := e_to_c (3 * j + 3) (A + 6 * j + 8) 0
    simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp [Q])

theorem trans_mod2 (j A : ℕ) :
    ⟨A + 3 * j + 5, 0, 3 * j + 3, 0, 0⟩ [fm]⊢⁺
    ⟨A + 6 * j + 10, 0, 3 * j + 4, 0, 0⟩ := by
  have p1 : ⟨A + 3 * j + 5, 0, 3 * j + 3, 0, 0⟩ [fm]⊢*
      ⟨A + 3 * j + 4, 0, 3 * j + 2, 2, 2⟩ := by
    rw [show A + 3 * j + 5 = (A + 3 * j + 4) + 1 from by ring,
        show 3 * j + 3 = (3 * j + 2) + 1 from by ring]
    step fm; step fm; finish
  have p2 : ⟨A + 3 * j + 4, 0, 3 * j + 2, 2, 2⟩ [fm]⊢*
      ⟨A + 2 * j + 4, 0, 2, 2 * j + 2, 3 * j + 2⟩ := by
    have h := opening_rounds j (A + 2 * j + 4) 2 1 2
    rw [show (A + 2 * j + 4) + j = A + 3 * j + 4 from by ring,
        show 2 + 3 * j = 3 * j + 2 from by ring,
        show 1 + 2 * j + 1 = 2 * j + 2 from by ring,
        show (1 + 1 : ℕ) = 2 from by ring] at h
    exact h
  have p3 : ⟨A + 2 * j + 4, 0, 2, 2 * j + 2, 3 * j + 2⟩ [fm]⊢*
      ⟨A + 2 * j + 4, 0, 0, 2 * j + 3, 3 * j + 4⟩ := by
    rw [show A + 2 * j + 4 = (A + 2 * j + 3) + 1 from by ring,
        show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
    have h := tail_c2 (A + 2 * j + 3) (2 * j + 1) (3 * j + 2)
    rw [show A + 2 * j + 3 + 1 = A + 2 * j + 4 from by ring,
        show 2 * j + 1 + 2 = 2 * j + 3 from by ring] at h
    exact h
  have p4 : ⟨A + 2 * j + 4, 0, 0, 2 * j + 3, 3 * j + 4⟩ [fm]⊢*
      ⟨A + 6 * j + 10, 0, 0, 0, 3 * j + 4⟩ := by
    rw [show A + 2 * j + 4 = (A + 2 * j + 3) + 1 from by ring]
    have h := r3r2_drain (2 * j + 3) (A + 2 * j + 3) (3 * j + 4)
    rw [show A + 2 * j + 3 + 2 * (2 * j + 3) + 1 = A + 6 * j + 10 from by ring] at h
    exact h
  have p5 : ⟨A + 6 * j + 10, 0, 0, 0, 3 * j + 4⟩ [fm]⊢*
      ⟨A + 6 * j + 10, 0, 3 * j + 4, 0, 0⟩ := by
    have h := e_to_c (3 * j + 4) (A + 6 * j + 10) 0
    simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 1, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A c, q = ⟨A + c + 3, 0, c + 1, 0, 0⟩)
  · rintro q ⟨A, c, rfl⟩
    have hmod : c % 3 < 3 := Nat.mod_lt _ (by omega)
    have hdiv : c = 3 * (c / 3) + c % 3 := (Nat.div_add_mod c 3).symm
    interval_cases (c % 3)
    · obtain ⟨j, rfl⟩ := Nat.dvd_of_mod_eq_zero (by omega : c % 3 = 0)
      refine ⟨⟨A + 6 * j + 6, 0, 3 * j + 2, 0, 0⟩,
              ⟨A + 3 * j + 2, 3 * j + 1, by ring_nf⟩, ?_⟩
      exact trans_mod0 j A
    · have ⟨j, hj⟩ : ∃ j, c = 3 * j + 1 := ⟨c / 3, by omega⟩
      subst hj
      refine ⟨⟨A + 6 * j + 8, 0, 3 * j + 3, 0, 0⟩,
              ⟨A + 3 * j + 3, 3 * j + 2, by ring_nf⟩, ?_⟩
      exact trans_mod1 j A
    · have ⟨j, hj⟩ : ∃ j, c = 3 * j + 2 := ⟨c / 3, by omega⟩
      subst hj
      refine ⟨⟨A + 6 * j + 10, 0, 3 * j + 4, 0, 0⟩,
              ⟨A + 3 * j + 4, 3 * j + 3, by ring_nf⟩, ?_⟩
      exact trans_mod2 j A
  · exact ⟨0, 0, by simp⟩

end Sz22_2003_unofficial_1611
