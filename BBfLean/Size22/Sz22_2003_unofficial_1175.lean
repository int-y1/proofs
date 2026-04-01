import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1175: [5/6, 49/2, 44/35, 3/11, 165/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  1  0  0 -1
 0  1  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1175

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

theorem e_to_b : ∀ k b, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

theorem round_chain_even : ∀ k c d, ⟨0, 2 * k, c + 1, d + k, c + 1⟩ [fm]⊢* ⟨0, 0, c + k + 1, d, c + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d); ring_nf; finish

theorem round_chain_odd : ∀ k c d, ⟨0, 2 * k + 1, c + 1, d + k, c + 1⟩ [fm]⊢* ⟨0, 1, c + k + 1, d, c + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) d); ring_nf; finish

theorem b1_finish : ⟨0, 1, c + 1, d + 1, c + 1⟩ [fm]⊢* ⟨0, 0, c + 1, d + 2, c + 2⟩ := by
  step fm; step fm; step fm; finish

theorem drain : ∀ c d e, ⟨0, 0, c + 1, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * c + 4, e + c + 1⟩ := by
  intro c; induction' c with c ih <;> intro d e
  · step fm; step fm; step fm; finish
  · step fm; step fm; step fm
    rw [show d + 2 + 2 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d + 3) (e + 1)); ring_nf; finish

-- Even e = 2m: (0, 0, 0, d+2m+2, 2m) →⁺ (0, 0, 0, d+4m+5, 2m+3)
theorem main_even (m : ℕ) :
    ⟨0, 0, 0, d + 2 * m + 2, 2 * m⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 4 * m + 5, 2 * m + 3⟩ := by
  -- R4 chain
  have h1 : ⟨0, 0, 0, d + 2 * m + 2, 2 * m⟩ [fm]⊢* ⟨0, 2 * m, 0, d + 2 * m + 2, 0⟩ := by
    have := e_to_b (2 * m) 0 (d := d + 2 * m + 2)
    simpa using this
  -- R5 step
  have h2 : (fm ⟨0, 2 * m, 0, d + 2 * m + 2, 0⟩ = some ⟨0, 2 * m + 1, 1, d + 2 * m + 1, 1⟩) := by
    show fm ⟨0, 2 * m, 0, (d + 2 * m + 1) + 1, 0⟩ = some _
    simp [fm]
  -- Round chain odd (m rounds)
  have h3 : ⟨0, 2 * m + 1, 0 + 1, (d + m + 1) + m, 0 + 1⟩ [fm]⊢*
      ⟨0, 1, 0 + m + 1, d + m + 1, 0 + m + 1⟩ :=
    round_chain_odd m 0 (d + m + 1)
  have h3' : ⟨0, 2 * m + 1, 1, d + 2 * m + 1, 1⟩ [fm]⊢*
      ⟨0, 1, m + 1, d + m + 1, m + 1⟩ := by
    rwa [show (0 : ℕ) + 1 = 1 from by omega,
         show (d + m + 1) + m = d + 2 * m + 1 from by omega,
         show 0 + m + 1 = m + 1 from by omega] at h3
  -- b1_finish
  have h4 : ⟨0, 1, m + 1, d + m + 1, m + 1⟩ [fm]⊢* ⟨0, 0, m + 1, d + m + 2, m + 2⟩ := by
    rw [show d + m + 1 = (d + m) + 1 from by omega]
    exact b1_finish (c := m) (d := d + m)
  -- Drain
  have h5 : ⟨0, 0, m + 1, d + m + 2, m + 2⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * m + 5, 2 * m + 3⟩ := by
    rw [show d + m + 2 = (d + m + 1) + 1 from by omega]
    have := drain m (d + m + 1) (m + 2)
    rw [show d + m + 1 + 3 * m + 4 = d + 4 * m + 5 from by omega,
        show m + 2 + m + 1 = 2 * m + 3 from by omega] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2 (stepStar_trans h3' (stepStar_trans h4 h5)))

-- Odd e = 2m+1: (0, 0, 0, d+2m+3, 2m+1) →⁺ (0, 0, 0, d+4m+7, 2m+4)
theorem main_odd (m : ℕ) :
    ⟨0, 0, 0, d + 2 * m + 3, 2 * m + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 4 * m + 7, 2 * m + 4⟩ := by
  -- R4 chain
  have h1 : ⟨0, 0, 0, d + 2 * m + 3, 2 * m + 1⟩ [fm]⊢* ⟨0, 2 * m + 1, 0, d + 2 * m + 3, 0⟩ := by
    have := e_to_b (2 * m + 1) 0 (d := d + 2 * m + 3)
    simpa using this
  -- R5 step
  have h2 : (fm ⟨0, 2 * m + 1, 0, d + 2 * m + 3, 0⟩ = some ⟨0, 2 * m + 2, 1, d + 2 * m + 2, 1⟩) := by
    show fm ⟨0, 2 * m + 1, 0, (d + 2 * m + 2) + 1, 0⟩ = some _
    simp [fm]
  -- Round chain even (m+1 rounds)
  have h3 : ⟨0, 2 * (m + 1), 0 + 1, (d + m + 1) + (m + 1), 0 + 1⟩ [fm]⊢*
      ⟨0, 0, 0 + (m + 1) + 1, d + m + 1, 0 + (m + 1) + 1⟩ :=
    round_chain_even (m + 1) 0 (d + m + 1)
  have h3' : ⟨0, 2 * m + 2, 1, d + 2 * m + 2, 1⟩ [fm]⊢*
      ⟨0, 0, m + 2, d + m + 1, m + 2⟩ := by
    rwa [show (0 : ℕ) + 1 = 1 from by omega,
         show (d + m + 1) + (m + 1) = d + 2 * m + 2 from by omega,
         show 2 * (m + 1) = 2 * m + 2 from by omega,
         show 0 + (m + 1) + 1 = m + 2 from by omega] at h3
  -- Drain
  have h4 : ⟨0, 0, m + 2, d + m + 1, m + 2⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * m + 7, 2 * m + 4⟩ := by
    rw [show m + 2 = (m + 1) + 1 from by omega,
        show d + m + 1 = (d + m) + 1 from by omega]
    have := drain (m + 1) (d + m) ((m + 1) + 1)
    rw [show d + m + 3 * (m + 1) + 4 = d + 4 * m + 7 from by omega,
        show (m + 1) + 1 + (m + 1) + 1 = 2 * m + 4 from by omega] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2 (stepStar_trans h3' h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ e + 2)
  · intro c ⟨d, e, hq, hd⟩; subst hq
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 * m + 2 := ⟨d - 2 * m - 2, by omega⟩
      exact ⟨⟨0, 0, 0, d' + 4 * m + 5, 2 * m + 3⟩,
        ⟨d' + 4 * m + 5, 2 * m + 3, rfl, by omega⟩, main_even m⟩
    · subst hm
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 * m + 3 := ⟨d - 2 * m - 3, by omega⟩
      exact ⟨⟨0, 0, 0, d' + 4 * m + 7, 2 * m + 4⟩,
        ⟨d' + 4 * m + 7, 2 * m + 4, rfl, by omega⟩, main_odd m⟩
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1175
