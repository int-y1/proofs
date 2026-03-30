import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1054

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem e_drain : ∀ k, ∀ b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

theorem r1r1r3_chain : ∀ k, ∀ c d e,
    ⟨2, 4 * k + 3, c, d + k, e⟩ [fm]⊢* ⟨2, 3, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 4 * (k + 1) + 3 = (4 * k + 3) + 2 + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

theorem b3_drain : ∀ c d e, ⟨2, 3, c + 1, d, e⟩ [fm]⊢* ⟨2, 0, c + 1, d, e + 3⟩ := by
  intro c d e
  step fm; step fm; step fm
  step fm; step fm; step fm
  step fm; step fm; step fm
  finish

theorem c_drain : ∀ k, ∀ d e, ⟨2, 0, k, d, e⟩ [fm]⊢* ⟨2, 0, 0, d + k, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; step fm; step fm
    step fm; step fm; step fm
    step fm; step fm; step fm
    apply stepStar_trans (ih (d + 1) (e + 3))
    ring_nf; finish

theorem main_trans (n : ℕ) : ⟨2, 0, 0, n, 4 * n + 3⟩ [fm]⊢⁺ ⟨2, 0, 0, n + 1, 4 * n + 7⟩ := by
  have h1 : ⟨2, 0, 0, n, 4 * n + 3⟩ [fm]⊢ ⟨1, 1, 0, n + 1, 4 * n + 3⟩ := by simp [fm]
  have h2 : ⟨1, 1, 0, n + 1, 4 * n + 3⟩ [fm]⊢ ⟨0, 2, 0, n + 2, 4 * n + 3⟩ := by simp [fm]
  have h3 : ⟨0, 2, 0, n + 2, 4 * n + 3⟩ [fm]⊢* ⟨0, 4 * n + 5, 0, n + 2, 0⟩ := by
    have := e_drain (4 * n + 3) 2 (n + 2)
    rw [show 2 + (4 * n + 3) = 4 * n + 5 from by ring] at this
    exact this
  have h4 : ⟨0, 4 * n + 5, 0, n + 2, 0⟩ [fm]⊢ ⟨1, 4 * n + 5, 1, n + 1, 0⟩ := by simp [fm]
  have h5 : ⟨1, 4 * n + 5, 1, n + 1, 0⟩ [fm]⊢* ⟨2, 4 * n + 3, 1, n, 1⟩ := by
    rw [show 4 * n + 5 = (4 * n + 3) + 2 from by ring]
    step fm; step fm; finish
  have h6 : ⟨2, 4 * n + 3, 1, n, 1⟩ [fm]⊢* ⟨2, 3, n + 1, 0, n + 1⟩ := by
    have := r1r1r3_chain n 1 0 1
    simp only [Nat.zero_add, Nat.add_comm 1 n] at this
    exact this
  have h7 : ⟨2, 3, n + 1, 0, n + 1⟩ [fm]⊢* ⟨2, 0, n + 1, 0, n + 4⟩ := by
    have := b3_drain n 0 (n + 1)
    rw [show n + 1 + 3 = n + 4 from by ring] at this
    exact this
  have h8 : ⟨2, 0, n + 1, 0, n + 4⟩ [fm]⊢* ⟨2, 0, 0, n + 1, 4 * n + 7⟩ := by
    have := c_drain (n + 1) 0 (n + 4)
    rw [show 0 + (n + 1) = n + 1 from by ring,
        show n + 4 + 3 * (n + 1) = 4 * n + 7 from by ring] at this
    exact this
  exact step_stepStar_stepPlus h1
    (stepStar_trans (step_stepStar h2)
      (stepStar_trans h3
        (stepStar_trans (step_stepStar h4)
          (stepStar_trans h5
            (stepStar_trans h6
              (stepStar_trans h7 h8))))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2, 0, 0, n, 4 * n + 3⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1054
