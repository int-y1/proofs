import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1048

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c+1, d⟩
  | ⟨a, b, c+2, d+1⟩ => some ⟨a+3, b, c, d⟩
  | ⟨a, b+3, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a+1, b, c, d+2⟩
  | _ => none

theorem r4r1r3_chain : ∀ k, ∀ d,
    ⟨(0 : ℕ), 2 * k + 3, 0, d⟩ [fm]⊢* ⟨0, 3, 0, d + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · ring_nf; finish
  · rw [show 2 * (k + 1) + 3 = (2 * k + 4) + 1 from by ring]
    step fm; step fm
    rw [show 2 * k + 4 + 2 = (2 * k + 3) + 3 from by ring]
    step fm
    apply stepStar_trans (ih (d + 2))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ b c,
    ⟨(0 : ℕ), b, c + 2, k⟩ [fm]⊢* ⟨0, b + 6 * k, c + k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · ring_nf; finish
  · step fm; step fm; step fm; step fm
    have := ih (b + 6) (c + 1)
    convert this using 2; ring_nf

theorem r3_chain : ∀ k, ∀ b,
    ⟨(0 : ℕ), b + 3 * k, k, 0⟩ [fm]⊢* ⟨0, b, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · ring_nf; finish
  · rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring]
    step fm
    exact ih b

theorem middle_steps (b : ℕ) :
    ⟨(0 : ℕ), 3, 0, 2 * b⟩ [fm]⊢* ⟨0, 3, 2, 2 * b + 6⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem main_trans (b : ℕ) :
    ⟨(0 : ℕ), 3, 0, 2 * b⟩ [fm]⊢⁺ ⟨0, 3, 0, 2 * (3 * b + 6)⟩ := by
  have h1 : ⟨(0 : ℕ), 3, 2, 2 * b + 6⟩ [fm]⊢*
      ⟨0, 12 * b + 39, 2 * b + 8, 0⟩ := by
    have := r2r1_chain (2 * b + 6) 3 0
    convert this using 2; ring_nf
  have h2 : ⟨(0 : ℕ), 12 * b + 39, 2 * b + 8, 0⟩ [fm]⊢*
      ⟨0, 6 * b + 15, 0, 0⟩ := by
    have := r3_chain (2 * b + 8) (6 * b + 15)
    convert this using 2; ring_nf
  have h3 : ⟨(0 : ℕ), 6 * b + 15, 0, 0⟩ [fm]⊢*
      ⟨0, 3, 0, 2 * (3 * b + 6)⟩ := by
    have := r4r1r3_chain (3 * b + 6) 0
    convert this using 2; ring_nf
  apply stepStar_stepPlus
  · exact stepStar_trans (middle_steps b)
      (stepStar_trans h1 (stepStar_trans h2 h3))
  · intro heq
    have := congr_arg (fun q : Q ↦ q.2.2.2) heq
    simp at this; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 0⟩) (by execute fm 15)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun b ↦ ⟨0, 3, 0, 2 * b⟩) 0
  intro b
  exact ⟨3 * b + 6, main_trans b⟩

end Sz22_2003_unofficial_1048
