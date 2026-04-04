import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1601: [77/15, 14/3, 9/110, 5/7, 33/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  1  0
-1  2 -1  0 -1
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1601

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c+1, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r311_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C + 3 * k, D, E + (1 : ℕ)⟩ [fm]⊢* ⟨A, 0, C, D + 2 * k, E + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 3 * (k + 1) = (C + 3 * k + 2) + 1 from by ring]
    step fm
    rw [show C + 3 * k + 2 = (C + 3 * k + 1) + 1 from by ring]
    step fm
    step fm
    rw [show D + 2 * (k + 1) = (D + 2) + 2 * k from by ring,
        show E + (k + 1) + 1 = (E + 1) + k + 1 from by ring]
    exact ih A C (D + 2) (E + 1)

theorem tail_c1 : ∀ A D E,
    ⟨A + 1, 0, 1, D, E + (1 : ℕ)⟩ [fm]⊢* ⟨A + 2, 0, 0, D + 2, E⟩ := by
  intro A D E
  step fm; step fm; step fm; ring_nf; finish

theorem tail_c2 : ∀ A D E,
    ⟨A + 1, 0, 2, D, E + (1 : ℕ)⟩ [fm]⊢* ⟨A + 1, 0, 0, D + 2, E + 1⟩ := by
  intro A D E
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm; ring_nf; finish

theorem cycle_chain : ∀ k, ∀ A D,
    ⟨A + 1, 0, 0, D + 1, k + (1 : ℕ)⟩ [fm]⊢* ⟨A + k + 2, 0, 0, D + k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · step fm; step fm; step fm; step fm; ring_nf; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show A + 1 + 1 = (A + 1) + 1 from by ring,
        show D + 1 + 1 = (D + 1) + 1 from by ring,
        show A + (k + 1) + 2 = (A + 1) + k + 2 from by ring,
        show D + (k + 1) + 2 = (D + 1) + k + 2 from by ring]
    exact ih (A + 1) (D + 1)

theorem d_to_c : ∀ k c, ⟨a, 0, c, k, (0 : ℕ)⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1)); ring_nf; finish

theorem main_trans_mod0 (m : ℕ) :
    ⟨3 * m + 2, 0, 6 * m + 2, 0, (0 : ℕ)⟩ [fm]⊢⁺ ⟨3 * m + 3, 0, 6 * m + 4, 0, 0⟩ := by
  have p1 : ⟨3 * m + 2, 0, 6 * m + 2, 0, (0 : ℕ)⟩ [fm]⊢* ⟨3 * m + 1, 0, 6 * m + 1, 1, 2⟩ := by
    rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring,
        show 6 * m + 2 = (6 * m + 1) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  have p2 : ⟨3 * m + 1, 0, 6 * m + 1, 1, (2 : ℕ)⟩ [fm]⊢* ⟨m + 1, 0, 1, 4 * m + 1, 2 * m + 2⟩ := by
    have h := r311_chain (2 * m) (m + 1) 1 1 1
    rw [show m + 1 + 2 * m = 3 * m + 1 from by ring,
        show 1 + 3 * (2 * m) = 6 * m + 1 from by ring,
        show (1 + 1 : ℕ) = 2 from by ring,
        show 1 + 2 * (2 * m) = 4 * m + 1 from by ring,
        show 1 + 2 * m + 1 = 2 * m + 2 from by ring] at h
    exact h
  have p3 : ⟨m + 1, 0, 1, 4 * m + 1, 2 * m + (2 : ℕ)⟩ [fm]⊢* ⟨m + 2, 0, 0, 4 * m + 3, 2 * m + 1⟩ := by
    rw [show m + 1 = m + 1 from rfl,
        show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
    have h := tail_c1 m (4 * m + 1) (2 * m + 1)
    rw [show m + 2 = m + 2 from rfl,
        show 4 * m + 1 + 2 = 4 * m + 3 from by ring] at h
    exact h
  have p4 : ⟨m + 2, 0, 0, 4 * m + 3, 2 * m + (1 : ℕ)⟩ [fm]⊢* ⟨3 * m + 3, 0, 0, 6 * m + 4, 0⟩ := by
    rw [show m + 2 = (m + 1) + 1 from by ring,
        show 4 * m + 3 = (4 * m + 2) + 1 from by ring,
        show 2 * m + 1 = 2 * m + 1 from rfl]
    have h := cycle_chain (2 * m) (m + 1) (4 * m + 2)
    rw [show m + 1 + 2 * m + 2 = 3 * m + 3 from by ring,
        show 4 * m + 2 + 2 * m + 2 = 6 * m + 4 from by ring] at h
    exact h
  have p5 : ⟨3 * m + 3, 0, 0, 6 * m + 4, (0 : ℕ)⟩ [fm]⊢* ⟨3 * m + 3, 0, 6 * m + 4, 0, 0⟩ := by
    have h := d_to_c (a := 3 * m + 3) (6 * m + 4) 0; simpa using h
  have p_star := stepStar_trans (stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4) p5
  exact stepStar_stepPlus p_star (by simp [Q])

theorem main_trans_mod1 (m : ℕ) :
    ⟨3 * m + 3, 0, 6 * m + 4, 0, (0 : ℕ)⟩ [fm]⊢⁺ ⟨3 * m + 4, 0, 6 * m + 6, 0, 0⟩ := by
  have p1 : ⟨3 * m + 3, 0, 6 * m + 4, 0, (0 : ℕ)⟩ [fm]⊢* ⟨3 * m + 2, 0, 6 * m + 3, 1, 2⟩ := by
    rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring,
        show 6 * m + 4 = (6 * m + 3) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  have p2 : ⟨3 * m + 2, 0, 6 * m + 3, 1, (2 : ℕ)⟩ [fm]⊢* ⟨m + 1, 0, 0, 4 * m + 3, 2 * m + 3⟩ := by
    have h := r311_chain (2 * m + 1) (m + 1) 0 1 1
    rw [show m + 1 + (2 * m + 1) = 3 * m + 2 from by ring,
        show 0 + 3 * (2 * m + 1) = 6 * m + 3 from by ring,
        show (1 + 1 : ℕ) = 2 from by ring,
        show 1 + 2 * (2 * m + 1) = 4 * m + 3 from by ring,
        show 1 + (2 * m + 1) + 1 = 2 * m + 3 from by ring] at h
    exact h
  have p3 : ⟨m + 1, 0, 0, 4 * m + 3, 2 * m + (3 : ℕ)⟩ [fm]⊢* ⟨3 * m + 4, 0, 0, 6 * m + 6, 0⟩ := by
    rw [show m + 1 = m + 1 from rfl,
        show 4 * m + 3 = (4 * m + 2) + 1 from by ring,
        show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
    have h := cycle_chain (2 * m + 2) m (4 * m + 2)
    rw [show m + (2 * m + 2) + 2 = 3 * m + 4 from by ring,
        show 4 * m + 2 + (2 * m + 2) + 2 = 6 * m + 6 from by ring] at h
    exact h
  have p4 : ⟨3 * m + 4, 0, 0, 6 * m + 6, (0 : ℕ)⟩ [fm]⊢* ⟨3 * m + 4, 0, 6 * m + 6, 0, 0⟩ := by
    have h := d_to_c (a := 3 * m + 4) (6 * m + 6) 0; simpa using h
  have p_star := stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4
  exact stepStar_stepPlus p_star (by simp [Q])

theorem main_trans_mod2 (m : ℕ) :
    ⟨3 * m + 4, 0, 6 * m + 6, 0, (0 : ℕ)⟩ [fm]⊢⁺ ⟨3 * m + 5, 0, 6 * m + 8, 0, 0⟩ := by
  have p1 : ⟨3 * m + 4, 0, 6 * m + 6, 0, (0 : ℕ)⟩ [fm]⊢* ⟨3 * m + 3, 0, 6 * m + 5, 1, 2⟩ := by
    rw [show 3 * m + 4 = (3 * m + 3) + 1 from by ring,
        show 6 * m + 6 = (6 * m + 5) + 1 from by ring]
    step fm; step fm; ring_nf; finish
  have p2 : ⟨3 * m + 3, 0, 6 * m + 5, 1, (2 : ℕ)⟩ [fm]⊢* ⟨m + 2, 0, 2, 4 * m + 3, 2 * m + 3⟩ := by
    have h := r311_chain (2 * m + 1) (m + 2) 2 1 1
    rw [show m + 2 + (2 * m + 1) = 3 * m + 3 from by ring,
        show 2 + 3 * (2 * m + 1) = 6 * m + 5 from by ring,
        show (1 + 1 : ℕ) = 2 from by ring,
        show 1 + 2 * (2 * m + 1) = 4 * m + 3 from by ring,
        show 1 + (2 * m + 1) + 1 = 2 * m + 3 from by ring] at h
    exact h
  have p3 : ⟨m + 2, 0, 2, 4 * m + 3, 2 * m + (3 : ℕ)⟩ [fm]⊢* ⟨m + 2, 0, 0, 4 * m + 5, 2 * m + 3⟩ := by
    rw [show m + 2 = (m + 1) + 1 from by ring,
        show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
    have h := tail_c2 (m + 1) (4 * m + 3) (2 * m + 2)
    rw [show m + 1 + 1 = m + 2 from by ring,
        show 4 * m + 3 + 2 = 4 * m + 5 from by ring,
        show 2 * m + 2 + 1 = 2 * m + 3 from by ring] at h
    exact h
  have p4 : ⟨m + 2, 0, 0, 4 * m + 5, 2 * m + (3 : ℕ)⟩ [fm]⊢* ⟨3 * m + 5, 0, 0, 6 * m + 8, 0⟩ := by
    rw [show m + 2 = (m + 1) + 1 from by ring,
        show 4 * m + 5 = (4 * m + 4) + 1 from by ring,
        show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
    have h := cycle_chain (2 * m + 2) (m + 1) (4 * m + 4)
    rw [show m + 1 + (2 * m + 2) + 2 = 3 * m + 5 from by ring,
        show 4 * m + 4 + (2 * m + 2) + 2 = 6 * m + 8 from by ring] at h
    exact h
  have p5 : ⟨3 * m + 5, 0, 0, 6 * m + 8, (0 : ℕ)⟩ [fm]⊢* ⟨3 * m + 5, 0, 6 * m + 8, 0, 0⟩ := by
    have h := d_to_c (a := 3 * m + 5) (6 * m + 8) 0; simpa using h
  have p_star := stepStar_trans (stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4) p5
  exact stepStar_stepPlus p_star (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨n + 2, 0, 2 * n + 2, 0, (0 : ℕ)⟩)
  · intro q ⟨n, hn⟩
    subst hn
    have hmod : n % 3 < 3 := Nat.mod_lt _ (by omega)
    have hdiv : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
    interval_cases (n % 3)
    · obtain ⟨j, rfl⟩ := Nat.dvd_of_mod_eq_zero (by omega : n % 3 = 0)
      clear hdiv hmod
      refine ⟨⟨3 * j + 3, 0, 6 * j + 4, 0, 0⟩, ⟨3 * j + 1, ?_⟩, ?_⟩
      · ring_nf
      · convert main_trans_mod0 j using 2; ring_nf
    · have ⟨j, hj⟩ : ∃ j, n = 3 * j + 1 := ⟨n / 3, by omega⟩
      subst hj; clear hdiv hmod
      refine ⟨⟨3 * j + 4, 0, 6 * j + 6, 0, 0⟩, ⟨3 * j + 2, ?_⟩, ?_⟩
      · ring_nf
      · convert main_trans_mod1 j using 2; ring_nf
    · have ⟨j, hj⟩ : ∃ j, n = 3 * j + 2 := ⟨n / 3, by omega⟩
      subst hj; clear hdiv hmod
      refine ⟨⟨3 * j + 5, 0, 6 * j + 8, 0, 0⟩, ⟨3 * j + 3, ?_⟩, ?_⟩
      · ring_nf
      · convert main_trans_mod2 j using 2; ring_nf
  · exact ⟨0, by simp⟩

end Sz22_2003_unofficial_1601
