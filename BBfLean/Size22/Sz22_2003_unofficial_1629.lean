import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1629

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C F,
    ⟨A, 0, C, 0, k, F⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro A C F
  · exists 0
  · rw [show C + (k + 1) = (C + 1) + k from by ring]
    step fm; exact ih A (C + 1) F

theorem r3r2r2_drain : ∀ k, ∀ A E F,
    ⟨A, 0, 0, k, E, k + F⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, 0, E, 2 * k + F⟩ := by
  intro k; induction' k with k ih <;> intro A E F
  · simp; exists 0
  · rw [show k + 1 + F = k + (F + 1) from by ring]
    step fm; step fm; step fm
    rw [show A + 2 * (k + 1) = (A + 2) + 2 * k from by ring,
        show 2 * (k + 1) + F = 2 * k + (F + 2) from by ring,
        show F + 1 + 1 = F + 2 from by ring]
    exact ih (A + 2) E (F + 2)

theorem r3r1r1_chain : ∀ k, ∀ A C D E F,
    ⟨A, 0, C + 2 * k, D + 1, E, F + k⟩ [fm]⊢*
    ⟨A, 0, C, D + k + 1, E + 2 * k, F⟩ := by
  intro k; induction' k with k ih <;> intro A C D E F
  · simp; exists 0
  · rw [show C + 2 * (k + 1) = C + 2 * k + 1 + 1 from by ring,
        show F + (k + 1) = F + k + 1 from by ring]
    step fm; step fm; step fm
    rw [show D + (k + 1) + 1 = (D + 1) + k + 1 from by ring,
        show E + 2 * (k + 1) = (E + 2) + 2 * k from by ring]
    exact ih A C (D + 1) (E + 2) F

theorem middle_even (m : ℕ) : ∀ A,
    ⟨A, 0, 2 * m, 1, 1, 4 * m + 1⟩ [fm]⊢*
    ⟨A + 2 * m + 2, 0, 0, 0, 2 * m + 1, 4 * m + 2⟩ := by
  intro A
  have p1 := r3r1r1_chain m A 0 0 1 (3 * m + 1)
  simp only [Nat.zero_add] at p1
  rw [show (3 * m + 1) + m = 4 * m + 1 from by ring,
      show 1 + 2 * m = 2 * m + 1 from by ring] at p1
  have p2 := r3r2r2_drain (m + 1) A (2 * m + 1) (2 * m)
  rw [show m + 1 + 2 * m = 3 * m + 1 from by ring,
      show A + 2 * (m + 1) = A + 2 * m + 2 from by ring,
      show 2 * (m + 1) + 2 * m = 4 * m + 2 from by ring] at p2
  exact stepStar_trans p1 p2

theorem r3r1r2_step : ∀ A m,
    ⟨A, 0, 1, m + 1, 2 * m + 1, 3 * m + 3⟩ [fm]⊢*
    ⟨A + 1, 0, 0, m + 1, 2 * m + 2, 3 * m + 3⟩ := by
  intro A m
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
  step fm; step fm; step fm
  ring_nf; finish

theorem middle_odd (m : ℕ) : ∀ A,
    ⟨A, 0, 2 * m + 1, 1, 1, 4 * m + 3⟩ [fm]⊢*
    ⟨A + 2 * m + 3, 0, 0, 0, 2 * m + 2, 4 * m + 4⟩ := by
  intro A
  have p1 := r3r1r1_chain m A 1 0 1 (3 * m + 3)
  rw [show (3 * m + 3) + m = 4 * m + 3 from by ring] at p1
  simp only [Nat.zero_add] at p1
  have hp1 : ⟨A, 0, 2 * m + 1, 1, 1, 4 * m + 3⟩ [fm]⊢*
      ⟨A, 0, 1, m + 1, 2 * m + 1, 3 * m + 3⟩ := by
    rw [show 2 * m + 1 = 1 + 2 * m from by ring]; exact p1
  have p2 := r3r1r2_step A m
  have p3 := r3r2r2_drain (m + 1) (A + 1) (2 * m + 2) (2 * m + 2)
  rw [show m + 1 + (2 * m + 2) = 3 * m + 3 from by ring,
      show (A + 1) + 2 * (m + 1) = A + 2 * m + 3 from by ring,
      show 2 * (m + 1) + (2 * m + 2) = 4 * m + 4 from by ring] at p3
  exact stepStar_trans (stepStar_trans hp1 p2) p3

theorem main_trans (A E : ℕ) :
    ⟨A + 1, 0, 0, 0, E, 2 * E⟩ [fm]⊢⁺
    ⟨A + E + 2, 0, 0, 0, E + 1, 2 * E + 2⟩ := by
  have p_r4 : ⟨A + 1, 0, 0, 0, E, 2 * E⟩ [fm]⊢*
      ⟨A + 1, 0, E, 0, 0, 2 * E⟩ := by
    have h := e_to_c E (A + 1) 0 (2 * E)
    simpa using h
  have p_r5 : ⟨A + 1, 0, E, 0, 0, 2 * E⟩ [fm]⊢*
      ⟨A, 0, E, 1, 1, 2 * E + 1⟩ := by
    step fm; finish
  have p_mid : ⟨A, 0, E, 1, 1, 2 * E + 1⟩ [fm]⊢*
      ⟨A + E + 2, 0, 0, 0, E + 1, 2 * E + 2⟩ := by
    rcases Nat.even_or_odd E with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      have h := middle_even m A
      rw [show 2 * (m + m) + 1 = 4 * m + 1 from by omega,
          show A + (m + m) + 2 = A + 2 * m + 2 from by omega,
          show m + m + 1 = 2 * m + 1 from by omega,
          show 2 * (m + m) + 2 = 4 * m + 2 from by omega,
          show m + m = 2 * m from by omega]
      exact h
    · subst hm
      have h := middle_odd m A
      rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by omega,
          show A + (2 * m + 1) + 2 = A + 2 * m + 3 from by omega,
          show 2 * m + 1 + 1 = 2 * m + 2 from by omega,
          show 2 * (2 * m + 1) + 2 = 4 * m + 4 from by omega]
      exact h
  have p_all := stepStar_trans (stepStar_trans p_r4 p_r5) p_mid
  exact stepStar_stepPlus p_all (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 1, 0, 0, 0, e, 2 * e⟩) ⟨0, 0⟩
  intro ⟨a, e⟩
  refine ⟨⟨a + e + 1, e + 1⟩, ?_⟩
  show ⟨a + 1, 0, 0, 0, e, 2 * e⟩ [fm]⊢⁺ ⟨a + e + 1 + 1, 0, 0, 0, e + 1, 2 * (e + 1)⟩
  rw [show a + e + 1 + 1 = a + e + 2 from by ring,
      show 2 * (e + 1) = 2 * e + 2 from by ring]
  exact main_trans a e

end Sz22_2003_unofficial_1629
