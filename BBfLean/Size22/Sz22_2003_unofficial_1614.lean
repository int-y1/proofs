import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1614

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C, ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm; apply stepStar_trans (ih A (C + 1)); ring_nf; finish

theorem r3r2_drain : ∀ k, ∀ A E, ⟨A + 1, 0, 0, k, E⟩ [fm]⊢* ⟨A + 2 * k + 1, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · simp; exists 0
  · step fm; step fm; step fm; step fm
    rw [show A + 2 * (k + 1) + 1 = (A + 2) + 2 * k + 1 from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    exact ih (A + 2) (E + 1)

theorem opening_round : ∀ A C D E,
    ⟨A + 1, 0, C + 3, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + 3, E + 4⟩ := by
  intro A C D E
  step fm
  rw [show C + 3 = (C + 2) + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show C + 2 = (C + 1) + 1 from by ring]
  step fm
  rw [show C + 1 = C + 1 from rfl, show (1 : ℕ) = 0 + 1 from by ring]
  step fm; ring_nf; finish

theorem opening_rounds : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C + 3 * k, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + 2 * k + 1, E + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 3 * (k + 1) = (C + 3 * k) + 3 from by ring]
    apply stepStar_trans (opening_round (A + k) (C + 3 * k) D E)
    rw [show D + 3 = (D + 2) + 1 from by ring]
    apply stepStar_trans (ih A C (D + 2) (E + 4))
    ring_nf; finish

theorem tail_c1 : ∀ A D E,
    ⟨A + 1, 0, 1, D + 1, E⟩ [fm]⊢* ⟨A + 2, 0, 0, D + 1, E + 2⟩ := by
  intro A D E
  step fm; step fm; step fm; step fm; ring_nf; finish

theorem tail_c2 : ∀ A D E,
    ⟨A + 1, 0, 2, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + 2, E + 3⟩ := by
  intro A D E
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  step fm; ring_nf; finish

theorem trans_c0 (n : ℕ) :
    ⟨n + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 1, 0, 0⟩ := by
  have p1 : ⟨n + 1, 0, 0, 0, 0⟩ [fm]⊢* ⟨n + 1, 0, 0, 1, 0⟩ := by
    rw [show n + 1 = n + 1 from rfl]
    step fm; step fm; finish
  have p2 : ⟨n + 1, 0, 0, 1, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 1⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    have h := r3r2_drain 1 n 0
    simp at h
    rw [show n + 2 * 1 + 1 = n + 3 from by ring] at h
    exact h
  have p3 : ⟨n + 3, 0, 0, 0, 1⟩ [fm]⊢* ⟨n + 3, 0, 1, 0, 0⟩ := by
    have h := e_to_c 1 (n + 3) 0; simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 p3)) (by simp [Q])

theorem trans_mod1 (j n : ℕ) :
    ⟨n + 3 * j + 2, 0, 3 * j + 1, 0, 0⟩ [fm]⊢⁺
    ⟨n + 6 * j + 5, 0, 6 * j + 3, 0, 0⟩ := by
  have p1 : ⟨n + 3 * j + 2, 0, 3 * j + 1, 0, 0⟩ [fm]⊢*
      ⟨n + 3 * j + 1, 0, 3 * j, 2, 1⟩ := by
    rw [show n + 3 * j + 2 = (n + 3 * j + 1) + 1 from by ring,
        show 3 * j + 1 = (3 * j) + 1 from by ring]
    step fm; step fm; finish
  have p2 : ⟨n + 3 * j + 1, 0, 3 * j, 2, 1⟩ [fm]⊢*
      ⟨n + 2 * j + 1, 0, 0, 2 * j + 2, 4 * j + 1⟩ := by
    have h := opening_rounds j (n + 2 * j + 1) 0 1 1
    rw [show (n + 2 * j + 1) + j = n + 3 * j + 1 from by ring,
        show 0 + 3 * j = 3 * j from by ring,
        show 1 + 2 * j + 1 = 2 * j + 2 from by ring,
        show 1 + 4 * j = 4 * j + 1 from by ring,
        show (1 + 1 : ℕ) = 2 from by ring] at h
    exact h
  have p3 : ⟨n + 2 * j + 1, 0, 0, 2 * j + 2, 4 * j + 1⟩ [fm]⊢*
      ⟨n + 6 * j + 5, 0, 0, 0, 6 * j + 3⟩ := by
    rw [show n + 2 * j + 1 = (n + 2 * j) + 1 from by ring]
    have h := r3r2_drain (2 * j + 2) (n + 2 * j) (4 * j + 1)
    rw [show n + 2 * j + 2 * (2 * j + 2) + 1 = n + 6 * j + 5 from by ring,
        show 4 * j + 1 + (2 * j + 2) = 6 * j + 3 from by ring] at h
    exact h
  have p4 : ⟨n + 6 * j + 5, 0, 0, 0, 6 * j + 3⟩ [fm]⊢*
      ⟨n + 6 * j + 5, 0, 6 * j + 3, 0, 0⟩ := by
    have h := e_to_c (6 * j + 3) (n + 6 * j + 5) 0
    simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3 p4)))
    (by simp only [Q, ne_eq, Prod.mk.injEq]; omega)

theorem trans_mod2 (j n : ℕ) :
    ⟨n + 3 * j + 3, 0, 3 * j + 2, 0, 0⟩ [fm]⊢⁺
    ⟨n + 6 * j + 7, 0, 6 * j + 5, 0, 0⟩ := by
  have p1 : ⟨n + 3 * j + 3, 0, 3 * j + 2, 0, 0⟩ [fm]⊢*
      ⟨n + 3 * j + 2, 0, 3 * j + 1, 2, 1⟩ := by
    rw [show n + 3 * j + 3 = (n + 3 * j + 2) + 1 from by ring,
        show 3 * j + 2 = (3 * j + 1) + 1 from by ring]
    step fm; step fm; finish
  have p2 : ⟨n + 3 * j + 2, 0, 3 * j + 1, 2, 1⟩ [fm]⊢*
      ⟨n + 2 * j + 2, 0, 1, 2 * j + 2, 4 * j + 1⟩ := by
    have h := opening_rounds j (n + 2 * j + 2) 1 1 1
    rw [show (n + 2 * j + 2) + j = n + 3 * j + 2 from by ring,
        show 1 + 3 * j = 3 * j + 1 from by ring,
        show 1 + 2 * j + 1 = 2 * j + 2 from by ring,
        show 1 + 4 * j = 4 * j + 1 from by ring,
        show (1 + 1 : ℕ) = 2 from by ring] at h
    exact h
  have p3 : ⟨n + 2 * j + 2, 0, 1, 2 * j + 2, 4 * j + 1⟩ [fm]⊢*
      ⟨n + 2 * j + 3, 0, 0, 2 * j + 2, 4 * j + 3⟩ := by
    rw [show n + 2 * j + 2 = (n + 2 * j + 1) + 1 from by ring,
        show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
    have h := tail_c1 (n + 2 * j + 1) (2 * j + 1) (4 * j + 1)
    rw [show n + 2 * j + 1 + 2 = n + 2 * j + 3 from by ring,
        show 2 * j + 1 + 1 = 2 * j + 2 from by ring,
        show 4 * j + 1 + 2 = 4 * j + 3 from by ring] at h
    exact h
  have p4 : ⟨n + 2 * j + 3, 0, 0, 2 * j + 2, 4 * j + 3⟩ [fm]⊢*
      ⟨n + 6 * j + 7, 0, 0, 0, 6 * j + 5⟩ := by
    rw [show n + 2 * j + 3 = (n + 2 * j + 2) + 1 from by ring]
    have h := r3r2_drain (2 * j + 2) (n + 2 * j + 2) (4 * j + 3)
    rw [show n + 2 * j + 2 + 2 * (2 * j + 2) + 1 = n + 6 * j + 7 from by ring,
        show 4 * j + 3 + (2 * j + 2) = 6 * j + 5 from by ring] at h
    exact h
  have p5 : ⟨n + 6 * j + 7, 0, 0, 0, 6 * j + 5⟩ [fm]⊢*
      ⟨n + 6 * j + 7, 0, 6 * j + 5, 0, 0⟩ := by
    have h := e_to_c (6 * j + 5) (n + 6 * j + 7) 0
    simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp only [Q, ne_eq, Prod.mk.injEq]; omega)

theorem trans_mod0 (j n : ℕ) :
    ⟨n + 3 * j + 4, 0, 3 * j + 3, 0, 0⟩ [fm]⊢⁺
    ⟨n + 6 * j + 9, 0, 6 * j + 7, 0, 0⟩ := by
  have p1 : ⟨n + 3 * j + 4, 0, 3 * j + 3, 0, 0⟩ [fm]⊢*
      ⟨n + 3 * j + 3, 0, 3 * j + 2, 2, 1⟩ := by
    rw [show n + 3 * j + 4 = (n + 3 * j + 3) + 1 from by ring,
        show 3 * j + 3 = (3 * j + 2) + 1 from by ring]
    step fm; step fm; finish
  have p2 : ⟨n + 3 * j + 3, 0, 3 * j + 2, 2, 1⟩ [fm]⊢*
      ⟨n + 2 * j + 3, 0, 2, 2 * j + 2, 4 * j + 1⟩ := by
    have h := opening_rounds j (n + 2 * j + 3) 2 1 1
    rw [show (n + 2 * j + 3) + j = n + 3 * j + 3 from by ring,
        show 2 + 3 * j = 3 * j + 2 from by ring,
        show 1 + 2 * j + 1 = 2 * j + 2 from by ring,
        show 1 + 4 * j = 4 * j + 1 from by ring,
        show (1 + 1 : ℕ) = 2 from by ring] at h
    exact h
  have p3 : ⟨n + 2 * j + 3, 0, 2, 2 * j + 2, 4 * j + 1⟩ [fm]⊢*
      ⟨n + 2 * j + 3, 0, 0, 2 * j + 3, 4 * j + 4⟩ := by
    rw [show n + 2 * j + 3 = (n + 2 * j + 2) + 1 from by ring,
        show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
    have h := tail_c2 (n + 2 * j + 2) (2 * j + 1) (4 * j + 1)
    rw [show n + 2 * j + 2 + 1 = n + 2 * j + 3 from by ring,
        show 2 * j + 1 + 2 = 2 * j + 3 from by ring,
        show 4 * j + 1 + 3 = 4 * j + 4 from by ring] at h
    exact h
  have p4 : ⟨n + 2 * j + 3, 0, 0, 2 * j + 3, 4 * j + 4⟩ [fm]⊢*
      ⟨n + 6 * j + 9, 0, 0, 0, 6 * j + 7⟩ := by
    rw [show n + 2 * j + 3 = (n + 2 * j + 2) + 1 from by ring]
    have h := r3r2_drain (2 * j + 3) (n + 2 * j + 2) (4 * j + 4)
    rw [show n + 2 * j + 2 + 2 * (2 * j + 3) + 1 = n + 6 * j + 9 from by ring,
        show 4 * j + 4 + (2 * j + 3) = 6 * j + 7 from by ring] at h
    exact h
  have p5 : ⟨n + 6 * j + 9, 0, 0, 0, 6 * j + 7⟩ [fm]⊢*
      ⟨n + 6 * j + 9, 0, 6 * j + 7, 0, 0⟩ := by
    have h := e_to_c (6 * j + 7) (n + 6 * j + 9) 0
    simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp only [Q, ne_eq, Prod.mk.injEq]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n c, q = ⟨n + c + 1, 0, c, 0, 0⟩)
  · rintro q ⟨n, c, rfl⟩
    rcases c with _ | c
    · refine ⟨⟨n + 3, 0, 1, 0, 0⟩, ⟨n + 1, 1, by ring_nf⟩, ?_⟩
      exact trans_c0 n
    · have h3 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
      rcases h3 with h0 | h1 | h2
      · obtain ⟨j, rfl⟩ : ∃ j, c = 3 * j := ⟨c / 3, by omega⟩
        refine ⟨⟨n + 6 * j + 5, 0, 6 * j + 3, 0, 0⟩,
                ⟨n + 1, 6 * j + 3, by ring_nf⟩, ?_⟩
        have : n + (3 * j + 1) + 1 = n + 3 * j + 2 := by ring
        rw [this]
        exact trans_mod1 j n
      · obtain ⟨j, rfl⟩ : ∃ j, c = 3 * j + 1 := ⟨c / 3, by omega⟩
        refine ⟨⟨n + 6 * j + 7, 0, 6 * j + 5, 0, 0⟩,
                ⟨n + 1, 6 * j + 5, by ring_nf⟩, ?_⟩
        have : n + (3 * j + 1 + 1) + 1 = n + 3 * j + 3 := by ring
        rw [this]
        exact trans_mod2 j n
      · obtain ⟨j, rfl⟩ : ∃ j, c = 3 * j + 2 := ⟨c / 3, by omega⟩
        refine ⟨⟨n + 6 * j + 9, 0, 6 * j + 7, 0, 0⟩,
                ⟨n + 1, 6 * j + 7, by ring_nf⟩, ?_⟩
        have : n + (3 * j + 2 + 1) + 1 = n + 3 * j + 4 := by ring
        rw [this]
        exact trans_mod0 j n
  · exact ⟨0, 0, by simp⟩

end Sz22_2003_unofficial_1614
