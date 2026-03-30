import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1057

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+2⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

private theorem fm_r5 (b c e : ℕ) : fm ⟨0, b, c, 0, e + 1⟩ = some ⟨1, b, c, 0, e⟩ := by
  unfold fm; rcases c with _ | c <;> rfl

private theorem fm_r2_b0 (c e : ℕ) : fm ⟨1, 0, c, 0, e⟩ = some ⟨0, 0, c, 3, e + 2⟩ := by
  unfold fm; rcases c with _ | c <;> rfl

private theorem fm_r2_b1 (c e : ℕ) : fm ⟨1, 1, c, 0, e⟩ = some ⟨0, 1, c, 3, e + 2⟩ := by
  unfold fm; rcases c with _ | c <;> rfl

theorem r5r1_chain : ∀ k c e,
    ⟨(0 : ℕ), k + k, c, 0, e + k⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · finish
  · rw [show (k + 1) + (k + 1) = k + k + 1 + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans
    · exact step_stepStar (fm_r5 (k + k + 1 + 1) c (e + k))
    apply stepStar_trans
    · show ⟨(1 : ℕ), k + k + 1 + 1, c, 0, e + k⟩ [fm]⊢* ⟨0, k + k, c + 1, 0, e + k⟩
      exact step_stepStar (by unfold fm; rfl)
    exact ih (c + 1) e

theorem r5r1_chain_odd : ∀ k c e,
    ⟨(0 : ℕ), k + k + 1, c, 0, e + k⟩ [fm]⊢* ⟨0, 1, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · finish
  · rw [show (k + 1) + (k + 1) + 1 = k + k + 1 + 1 + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans
    · exact step_stepStar (fm_r5 (k + k + 1 + 1 + 1) c (e + k))
    apply stepStar_trans
    · show ⟨(1 : ℕ), k + k + 1 + 1 + 1, c, 0, e + k⟩ [fm]⊢* ⟨0, k + k + 1, c + 1, 0, e + k⟩
      exact step_stepStar (by unfold fm; rfl)
    exact ih (c + 1) e

theorem r3r2_chain_b0 : ∀ k d e,
    ⟨(0 : ℕ), 0, k, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 1 + 2 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + 1 + 2 * (k + 1) = (d + 2) + 1 + 2 * k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; step fm
    exact ih (d + 2) (e + 2)

theorem r3r2_chain_b1 : ∀ k d e,
    ⟨(0 : ℕ), 1, k, d + 1, e⟩ [fm]⊢* ⟨0, 1, 0, d + 1 + 2 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + 1 + 2 * (k + 1) = (d + 2) + 1 + 2 * k from by ring,
        show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
    step fm; step fm
    exact ih (d + 2) (e + 2)

theorem r4_drain : ∀ k b e,
    ⟨(0 : ℕ), b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm
    exact ih (b + 1) e

theorem main_even (m E : ℕ) :
    ⟨(0 : ℕ), m + m, 0, 0, E + m + 1⟩ [fm]⊢⁺ ⟨0, m + m + 3, 0, 0, E + m + m + 2⟩ := by
  have h1 : ⟨(0 : ℕ), m + m, 0, 0, E + m + 1⟩ [fm]⊢* ⟨0, 0, m, 0, E + 1⟩ := by
    have := r5r1_chain m 0 (E + 1)
    simp only [Nat.zero_add] at this
    rwa [show (E + 1) + m = E + m + 1 from by ring] at this
  have h2 : ⟨(0 : ℕ), 0, m, 0, E + 1⟩ [fm]⊢ ⟨1, 0, m, 0, E⟩ :=
    fm_r5 0 m E
  have h3 : ⟨(1 : ℕ), 0, m, 0, E⟩ [fm]⊢ ⟨0, 0, m, 3, E + 2⟩ :=
    fm_r2_b0 m E
  have h4 : ⟨(0 : ℕ), 0, m, 3, E + 2⟩ [fm]⊢* ⟨0, 0, 0, m + m + 3, E + m + m + 2⟩ := by
    have := r3r2_chain_b0 m 2 (E + 2)
    rw [show 2 + 1 + 2 * m = m + m + 3 from by ring,
        show (E + 2) + 2 * m = E + m + m + 2 from by ring] at this
    exact this
  have h5 : ⟨(0 : ℕ), 0, 0, m + m + 3, E + m + m + 2⟩ [fm]⊢*
      ⟨0, m + m + 3, 0, 0, E + m + m + 2⟩ := by
    have := r4_drain (m + m + 3) 0 (E + m + m + 2)
    simp only [Nat.zero_add] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2
      (stepStar_trans (step_stepStar h3)
        (stepStar_trans h4 h5)))

theorem main_odd (m E : ℕ) :
    ⟨(0 : ℕ), m + m + 1, 0, 0, E + m + 1⟩ [fm]⊢⁺ ⟨0, m + m + 4, 0, 0, E + m + m + 2⟩ := by
  have h1 : ⟨(0 : ℕ), m + m + 1, 0, 0, E + m + 1⟩ [fm]⊢* ⟨0, 1, m, 0, E + 1⟩ := by
    have := r5r1_chain_odd m 0 (E + 1)
    simp only [Nat.zero_add] at this
    rwa [show (E + 1) + m = E + m + 1 from by ring] at this
  have h2 : ⟨(0 : ℕ), 1, m, 0, E + 1⟩ [fm]⊢ ⟨1, 1, m, 0, E⟩ :=
    fm_r5 1 m E
  have h3 : ⟨(1 : ℕ), 1, m, 0, E⟩ [fm]⊢ ⟨0, 1, m, 3, E + 2⟩ :=
    fm_r2_b1 m E
  have h4 : ⟨(0 : ℕ), 1, m, 3, E + 2⟩ [fm]⊢* ⟨0, 1, 0, m + m + 3, E + m + m + 2⟩ := by
    have := r3r2_chain_b1 m 2 (E + 2)
    rw [show 2 + 1 + 2 * m = m + m + 3 from by ring,
        show (E + 2) + 2 * m = E + m + m + 2 from by ring] at this
    exact this
  have h5 : ⟨(0 : ℕ), 1, 0, m + m + 3, E + m + m + 2⟩ [fm]⊢*
      ⟨0, m + m + 4, 0, 0, E + m + m + 2⟩ := by
    have := r4_drain (m + m + 3) 1 (E + m + m + 2)
    rw [show 1 + (m + m + 3) = m + m + 4 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2
      (stepStar_trans (step_stepStar h3)
        (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 0, 2⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b e, q = ⟨0, b, 0, 0, e⟩ ∧ b ≥ 3 ∧ e ≥ b / 2 + 1)
  · intro c ⟨b, e, hc, hb, he⟩
    subst hc
    rcases Nat.even_or_odd b with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      obtain ⟨E, rfl⟩ : ∃ E, e = E + m + 1 := ⟨e - m - 1, by omega⟩
      exact ⟨⟨0, m + m + 3, 0, 0, E + m + m + 2⟩,
             ⟨m + m + 3, E + m + m + 2, rfl, by omega, by omega⟩,
             main_even m E⟩
    · subst hm
      obtain ⟨E, rfl⟩ : ∃ E, e = E + m + 1 := ⟨e - m - 1, by omega⟩
      refine ⟨⟨0, m + m + 4, 0, 0, E + m + m + 2⟩,
             ⟨m + m + 4, E + m + m + 2, rfl, by omega, by omega⟩, ?_⟩
      rw [show 2 * m + 1 = m + m + 1 from by ring]
      exact main_odd m E
  · exact ⟨3, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1057
