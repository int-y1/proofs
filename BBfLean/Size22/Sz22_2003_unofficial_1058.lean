import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1058

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem a_drain : ∀ k, ∀ D E, ⟨k + 2, 0, 0, D, E⟩ [fm]⊢* ⟨2, 0, 0, D + k, E + k⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · exists 0
  · rw [show k + 1 + 2 = (k + 2) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (D + 1) (E + 1))
    ring_nf; finish

theorem e_drain : ∀ k, ∀ b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ C D E,
    ⟨2, 4 * k + 3, C, D + k, E⟩ [fm]⊢* ⟨2, 3, C + k, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · exists 0
  · rw [show 4 * (k + 1) + 3 = (4 * k + 3) + 2 + 2 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (C + 1) D (E + 1))
    ring_nf; finish

theorem b3_phase : ∀ C E, ⟨2, 3, C + 1, 0, E⟩ [fm]⊢* ⟨2, 0, C + 1, 0, E + 3⟩ := by
  intro C E
  step fm; step fm; step fm
  step fm; step fm; step fm
  step fm; step fm; step fm
  finish

theorem c_drain : ∀ k, ∀ A E,
    ⟨A + 2, 0, k, 0, E⟩ [fm]⊢* ⟨A + k + 2, 0, 0, 0, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · ring_nf; finish
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (A + 1) (E + 2))
    ring_nf; finish

theorem main_trans (a : ℕ) :
    ⟨a + 2, 0, 0, 0, 3 * a + 3⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 0, 3 * a + 6⟩ := by
  have h1 : ⟨a + 2, 0, 0, 0, 3 * a + 3⟩ [fm]⊢* ⟨2, 0, 0, a, 4 * a + 3⟩ := by
    have := a_drain a 0 (3 * a + 3)
    rw [show (0 : ℕ) + a = a from by ring,
        show 3 * a + 3 + a = 4 * a + 3 from by ring] at this
    exact this
  have h2 : ⟨2, 0, 0, a, 4 * a + 3⟩ [fm]⊢* ⟨0, 2, 0, a + 2, 4 * a + 3⟩ := by
    step fm; step fm; ring_nf; finish
  have h3 : ⟨0, 2, 0, a + 2, 4 * a + 3⟩ [fm]⊢* ⟨0, 4 * a + 5, 0, a + 2, 0⟩ := by
    have := e_drain (4 * a + 3) 2 (a + 2)
    rw [show 2 + (4 * a + 3) = 4 * a + 5 from by ring] at this
    exact this
  have h4 : ⟨0, 4 * a + 5, 0, a + 2, 0⟩ [fm]⊢* ⟨2, 4 * a + 3, 1, a, 1⟩ := by
    step fm; step fm; step fm; ring_nf; finish
  have h5 : ⟨2, 4 * a + 3, 1, a, 1⟩ [fm]⊢* ⟨2, 3, a + 1, 0, a + 1⟩ := by
    have := r1r1r2_chain a 1 0 1
    simp only [Nat.zero_add, Nat.add_comm 1 a] at this
    exact this
  have h6 : ⟨2, 3, a + 1, 0, a + 1⟩ [fm]⊢* ⟨2, 0, a + 1, 0, a + 4⟩ := by
    have := b3_phase a (a + 1)
    rw [show a + 1 + 3 = a + 4 from by ring] at this
    exact this
  have h7 : ⟨2, 0, a + 1, 0, a + 4⟩ [fm]⊢* ⟨a + 3, 0, 0, 0, 3 * a + 6⟩ := by
    have := c_drain (a + 1) 0 (a + 4)
    rw [show 0 + (a + 1) + 2 = a + 3 from by ring,
        show a + 4 + 2 * (a + 1) = 3 * a + 6 from by ring] at this
    exact this
  have hall : ⟨a + 2, 0, 0, 0, 3 * a + 3⟩ [fm]⊢* ⟨a + 3, 0, 0, 0, 3 * a + 6⟩ :=
    stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3
      (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 h7)))))
  exact stepStar_stepPlus hall (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun a ↦ ⟨a + 2, 0, 0, 0, 3 * a + 3⟩) 0
  intro a; exact ⟨a + 1, main_trans a⟩

end Sz22_2003_unofficial_1058
