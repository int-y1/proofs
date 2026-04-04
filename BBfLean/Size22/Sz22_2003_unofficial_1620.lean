import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1620

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C, ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm; apply stepStar_trans (ih A (C + 1)); ring_nf; finish

theorem r1_chain : ∀ k, ∀ A C D E, ⟨A, k, C + k, D, E⟩ [fm]⊢* ⟨A, 0, C, D + k, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · exists 0
  · rw [show C + (k + 1) = (C + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih A C (D + 1) (E + 1)); ring_nf; finish

theorem r3r2r2_drain : ∀ k, ∀ A E,
    ⟨A + 1, 0, 0, k + 1, E⟩ [fm]⊢* ⟨A + k + 2, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show A + (k + 1) + 2 = (A + 1) + k + 2 from by ring]
    exact ih (A + 1) E

theorem c_drain_even : ∀ k, ∀ A D E,
    ⟨A + k, 0, 2 * k, D + 1, E⟩ [fm]⊢* ⟨A, 0, 0, D + k + 1, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih A (D + 1) (E + 2))
    ring_nf; finish

theorem c_drain_odd : ∀ k, ∀ A D E,
    ⟨A + k + 1, 0, 2 * k + 1, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + k + 1, E + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show A + (k + 1) + 1 = (A + k + 1) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 + 1 = (2 * k + 1) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih A (D + 1) (E + 2))
    ring_nf; finish

theorem trans_odd (m : ℕ) :
    ⟨4 * m + 7, 0, 0, 0, 2 * m + 3⟩ [fm]⊢⁺ ⟨4 * m + 9, 0, 0, 0, 2 * m + 4⟩ := by
  have p1 : ⟨4 * m + 7, 0, 0, 0, 2 * m + 3⟩ [fm]⊢*
      ⟨4 * m + 7, 0, 2 * m + 3, 0, 0⟩ := by
    have h := e_to_c (2 * m + 3) (4 * m + 7) 0; simp at h; exact h
  have p2 : ⟨4 * m + 7, 0, 2 * m + 3, 0, 0⟩ [fm]⊢*
      ⟨4 * m + 6, 3, 2 * m + 3, 0, 1⟩ := by
    rw [show 4 * m + 7 = (4 * m + 6) + 1 from by ring]; step fm; finish
  have p3 : ⟨4 * m + 6, 3, 2 * m + 3, 0, 1⟩ [fm]⊢*
      ⟨4 * m + 6, 0, 2 * m, 3, 4⟩ := by
    rw [show 2 * m + 3 = (2 * m) + 3 from by ring]
    exact r1_chain 3 (4 * m + 6) (2 * m) 0 1
  have p4 : ⟨4 * m + 6, 0, 2 * m, 3, 4⟩ [fm]⊢*
      ⟨3 * m + 6, 0, 0, m + 3, 2 * m + 4⟩ := by
    rw [show 4 * m + 6 = (3 * m + 6) + m from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    have h := c_drain_even m (3 * m + 6) 2 4
    rw [show 2 + m + 1 = m + 3 from by ring,
        show 4 + 2 * m = 2 * m + 4 from by ring] at h
    exact h
  have p5 : ⟨3 * m + 6, 0, 0, m + 3, 2 * m + 4⟩ [fm]⊢*
      ⟨4 * m + 9, 0, 0, 0, 2 * m + 4⟩ := by
    rw [show 3 * m + 6 = (3 * m + 5) + 1 from by ring,
        show m + 3 = (m + 2) + 1 from by ring]
    have h := r3r2r2_drain (m + 2) (3 * m + 5) (2 * m + 4)
    rw [show 3 * m + 5 + (m + 2) + 2 = 4 * m + 9 from by ring] at h
    exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp [Q])

theorem trans_even (m : ℕ) :
    ⟨4 * m + 9, 0, 0, 0, 2 * m + 4⟩ [fm]⊢⁺ ⟨4 * m + 11, 0, 0, 0, 2 * m + 5⟩ := by
  have p1 : ⟨4 * m + 9, 0, 0, 0, 2 * m + 4⟩ [fm]⊢*
      ⟨4 * m + 9, 0, 2 * m + 4, 0, 0⟩ := by
    have h := e_to_c (2 * m + 4) (4 * m + 9) 0; simp at h; exact h
  have p2 : ⟨4 * m + 9, 0, 2 * m + 4, 0, 0⟩ [fm]⊢*
      ⟨4 * m + 8, 3, 2 * m + 4, 0, 1⟩ := by
    rw [show 4 * m + 9 = (4 * m + 8) + 1 from by ring]; step fm; finish
  have p3 : ⟨4 * m + 8, 3, 2 * m + 4, 0, 1⟩ [fm]⊢*
      ⟨4 * m + 8, 0, 2 * m + 1, 3, 4⟩ := by
    rw [show 2 * m + 4 = (2 * m + 1) + 3 from by ring]
    exact r1_chain 3 (4 * m + 8) (2 * m + 1) 0 1
  have p4 : ⟨4 * m + 8, 0, 2 * m + 1, 3, 4⟩ [fm]⊢*
      ⟨3 * m + 8, 0, 0, m + 3, 2 * m + 5⟩ := by
    rw [show 4 * m + 8 = (3 * m + 7) + m + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    have h := c_drain_odd m (3 * m + 7) 2 4
    rw [show 3 * m + 7 + 1 = 3 * m + 8 from by ring,
        show 2 + m + 1 = m + 3 from by ring,
        show 4 + 2 * m + 1 = 2 * m + 5 from by ring] at h
    exact h
  have p5 : ⟨3 * m + 8, 0, 0, m + 3, 2 * m + 5⟩ [fm]⊢*
      ⟨4 * m + 11, 0, 0, 0, 2 * m + 5⟩ := by
    rw [show 3 * m + 8 = (3 * m + 7) + 1 from by ring,
        show m + 3 = (m + 2) + 1 from by ring]
    have h := r3r2r2_drain (m + 2) (3 * m + 7) (2 * m + 5)
    rw [show 3 * m + 7 + (m + 2) + 2 = 4 * m + 11 from by ring] at h
    exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp [Q])

theorem main_trans (n : ℕ) :
    ⟨2 * n + 7, 0, 0, 0, n + 3⟩ [fm]⊢⁺ ⟨2 * n + 9, 0, 0, 0, n + 4⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    show ⟨2 * (m + m) + 7, 0, 0, 0, m + m + 3⟩ [fm]⊢⁺ ⟨2 * (m + m) + 9, 0, 0, 0, m + m + 4⟩
    rw [show 2 * (m + m) + 7 = 4 * m + 7 from by ring,
        show m + m + 3 = 2 * m + 3 from by ring,
        show 2 * (m + m) + 9 = 4 * m + 9 from by ring,
        show m + m + 4 = 2 * m + 4 from by ring]
    exact trans_odd m
  · subst hm
    show ⟨2 * (2 * m + 1) + 7, 0, 0, 0, 2 * m + 1 + 3⟩ [fm]⊢⁺ ⟨2 * (2 * m + 1) + 9, 0, 0, 0, 2 * m + 1 + 4⟩
    rw [show 2 * (2 * m + 1) + 7 = 4 * m + 9 from by ring,
        show 2 * m + 1 + 3 = 2 * m + 4 from by ring,
        show 2 * (2 * m + 1) + 9 = 4 * m + 11 from by ring,
        show 2 * m + 1 + 4 = 2 * m + 5 from by ring]
    exact trans_even m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 3⟩) (by execute fm 24)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 7, 0, 0, 0, n + 3⟩) 0
  intro n; exists n + 1
  exact main_trans n

end Sz22_2003_unofficial_1620
