import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1621

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d+1, e⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C, ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · exists 0
  · step fm; apply stepStar_trans (ih A (C + 1)); ring_nf; finish

theorem r3r2r2_drain : ∀ k, ∀ A E,
    ⟨A + 1, 0, 0, k + 1, E⟩ [fm]⊢* ⟨A + k + 2, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show A + (k + 1) + 2 = (A + 1) + k + 2 from by ring]
    exact ih (A + 1) E

-- One round of R1, R1, R3:
-- (A+1, 2, C+2, D, E) -> (A+1, 1, C+1, D+1, E+1) -> (A+1, 0, C, D+2, E+2) -> (A, 2, C, D+1, E+2)
-- k rounds:
theorem r1r1r3_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 2, C + 2 * k, D, E⟩ [fm]⊢* ⟨A, 2, C, D + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k + 1) + 1 from by ring]
    step fm
    rw [show C + 2 * k + 1 = (C + 2 * k) + 1 from by ring]
    step fm
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring,
        show E + 1 + 1 = (E + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih A C (D + 1) (E + 2))
    ring_nf; finish

-- Odd tail: R3, R1, R2
-- (A+1, 0, 1, D+1, E) -> R3 -> (A, 2, 1, D, E) -> R1 -> (A, 1, 0, D+1, E+1) -> R2 -> (A+1, 0, 0, D+1, E+1)
theorem odd_tail : ∀ A D E,
    ⟨A + 1, 0, 1, D + 1, E⟩ [fm]⊢* ⟨A + 1, 0, 0, D + 1, E + 1⟩ := by
  intro A D E
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm; ring_nf; finish

-- Main transition for odd c: c = 2k+1
-- (4k+3, 0, 2k+1, 0, 0) ⊢⁺ (4k+5, 0, 2k+2, 0, 0)
theorem trans_odd (k : ℕ) :
    ⟨4 * k + 3, 0, 2 * k + 1, 0, 0⟩ [fm]⊢⁺ ⟨4 * k + 5, 0, 2 * k + 2, 0, 0⟩ := by
  -- R5: (4k+3, 0, 2k+1, 0, 0) -> (4k+2, 2, 2k+2, 1, 0)
  have p1 : ⟨4 * k + 3, 0, 2 * k + 1, 0, 0⟩ [fm]⊢*
      ⟨4 * k + 2, 2, 2 * k + 2, 1, 0⟩ := by
    rw [show 4 * k + 3 = (4 * k + 2) + 1 from by ring]; step fm; ring_nf; finish
  -- k rounds of R1R1R3: (4k+2, 2, 2k+2, 1, 0) -> (3k+2, 2, 2, k+1, 2k)
  have p2 : ⟨4 * k + 2, 2, 2 * k + 2, 1, 0⟩ [fm]⊢*
      ⟨3 * k + 2, 2, 2, k + 1, 2 * k⟩ := by
    rw [show 4 * k + 2 = (3 * k + 2) + k from by ring,
        show 2 * k + 2 = 2 + 2 * k from by ring]
    have h := r1r1r3_chain k (3 * k + 2) 2 1 0
    rw [show 1 + k = k + 1 from by ring, show 0 + 2 * k = 2 * k from by ring] at h
    exact h
  -- R1 pair: (3k+2, 2, 2, k+1, 2k) -> (3k+2, 0, 0, k+3, 2k+2)
  have p3 : ⟨3 * k + 2, 2, 2, k + 1, 2 * k⟩ [fm]⊢*
      ⟨3 * k + 2, 0, 0, k + 3, 2 * k + 2⟩ := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
    step fm; step fm; ring_nf; finish
  -- Drain d: (3k+2, 0, 0, k+3, 2k+2) -> (4k+5, 0, 0, 0, 2k+2)
  have p4 : ⟨3 * k + 2, 0, 0, k + 3, 2 * k + 2⟩ [fm]⊢*
      ⟨4 * k + 5, 0, 0, 0, 2 * k + 2⟩ := by
    rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring,
        show k + 3 = (k + 2) + 1 from by ring]
    have h := r3r2r2_drain (k + 2) (3 * k + 1) (2 * k + 2)
    rw [show 3 * k + 1 + (k + 2) + 2 = 4 * k + 5 from by ring] at h
    exact h
  -- R4 chain: (4k+5, 0, 0, 0, 2k+2) -> (4k+5, 0, 2k+2, 0, 0)
  have p5 : ⟨4 * k + 5, 0, 0, 0, 2 * k + 2⟩ [fm]⊢*
      ⟨4 * k + 5, 0, 2 * k + 2, 0, 0⟩ := by
    have h := e_to_c (2 * k + 2) (4 * k + 5) 0; simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 p5)))) (by simp [Q])

-- Main transition for even c: c = 2k+2
-- (4k+5, 0, 2k+2, 0, 0) ⊢⁺ (4k+7, 0, 2k+3, 0, 0)
theorem trans_even (k : ℕ) :
    ⟨4 * k + 5, 0, 2 * k + 2, 0, 0⟩ [fm]⊢⁺ ⟨4 * k + 7, 0, 2 * k + 3, 0, 0⟩ := by
  -- R5
  have p1 : ⟨4 * k + 5, 0, 2 * k + 2, 0, 0⟩ [fm]⊢*
      ⟨4 * k + 4, 2, 2 * k + 3, 1, 0⟩ := by
    rw [show 4 * k + 5 = (4 * k + 4) + 1 from by ring]; step fm; ring_nf; finish
  -- k rounds of R1R1R3
  have p2 : ⟨4 * k + 4, 2, 2 * k + 3, 1, 0⟩ [fm]⊢*
      ⟨3 * k + 4, 2, 3, k + 1, 2 * k⟩ := by
    rw [show 4 * k + 4 = (3 * k + 4) + k from by ring,
        show 2 * k + 3 = 3 + 2 * k from by ring]
    have h := r1r1r3_chain k (3 * k + 4) 3 1 0
    rw [show 1 + k = k + 1 from by ring, show 0 + 2 * k = 2 * k from by ring] at h
    exact h
  -- R1 pair: (3k+4, 2, 3, k+1, 2k) -> (3k+4, 0, 1, k+3, 2k+2)
  have p3 : ⟨3 * k + 4, 2, 3, k + 1, 2 * k⟩ [fm]⊢*
      ⟨3 * k + 4, 0, 1, k + 3, 2 * k + 2⟩ := by
    rw [show (3 : ℕ) = 1 + 1 + 1 from by ring]
    step fm; step fm; ring_nf; finish
  -- Odd tail: (3k+4, 0, 1, k+3, 2k+2) -> (3k+4, 0, 0, k+3, 2k+3)
  have p4 : ⟨3 * k + 4, 0, 1, k + 3, 2 * k + 2⟩ [fm]⊢*
      ⟨3 * k + 4, 0, 0, k + 3, 2 * k + 3⟩ := by
    rw [show 3 * k + 4 = (3 * k + 3) + 1 from by ring,
        show k + 3 = (k + 2) + 1 from by ring]
    have h := odd_tail (3 * k + 3) (k + 2) (2 * k + 2)
    rw [show 3 * k + 3 + 1 = 3 * k + 4 from by ring,
        show k + 2 + 1 = k + 3 from by ring,
        show 2 * k + 2 + 1 = 2 * k + 3 from by ring] at h
    exact h
  -- Drain d
  have p5 : ⟨3 * k + 4, 0, 0, k + 3, 2 * k + 3⟩ [fm]⊢*
      ⟨4 * k + 7, 0, 0, 0, 2 * k + 3⟩ := by
    rw [show 3 * k + 4 = (3 * k + 3) + 1 from by ring,
        show k + 3 = (k + 2) + 1 from by ring]
    have h := r3r2r2_drain (k + 2) (3 * k + 3) (2 * k + 3)
    rw [show 3 * k + 3 + (k + 2) + 2 = 4 * k + 7 from by ring] at h
    exact h
  -- R4 chain
  have p6 : ⟨4 * k + 7, 0, 0, 0, 2 * k + 3⟩ [fm]⊢*
      ⟨4 * k + 7, 0, 2 * k + 3, 0, 0⟩ := by
    have h := e_to_c (2 * k + 3) (4 * k + 7) 0; simp at h; exact h
  exact stepStar_stepPlus (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3
    (stepStar_trans p4 (stepStar_trans p5 p6))))) (by simp [Q])

theorem main_trans (n : ℕ) :
    ⟨2 * n + 3, 0, n + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, n + 2, 0, 0⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    show ⟨2 * (k + k) + 3, 0, k + k + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * (k + k) + 5, 0, k + k + 2, 0, 0⟩
    rw [show 2 * (k + k) + 3 = 4 * k + 3 from by ring,
        show k + k + 1 = 2 * k + 1 from by ring,
        show 2 * (k + k) + 5 = 4 * k + 5 from by ring,
        show k + k + 2 = 2 * k + 2 from by ring]
    exact trans_odd k
  · subst hk
    show ⟨2 * (2 * k + 1) + 3, 0, 2 * k + 1 + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * (2 * k + 1) + 5, 0, 2 * k + 1 + 2, 0, 0⟩
    rw [show 2 * (2 * k + 1) + 3 = 4 * k + 5 from by ring,
        show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
        show 2 * (2 * k + 1) + 5 = 4 * k + 7 from by ring,
        show 2 * k + 1 + 2 = 2 * k + 3 from by ring]
    exact trans_even k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 1, 0, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, n + 1, 0, 0⟩) 0
  intro n; exists n + 1
  exact main_trans n

end Sz22_2003_unofficial_1621
