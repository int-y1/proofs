import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1608

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C F,
    ⟨A, 0, C, 0, k, F⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro A C F
  · exists 0
  · rw [show C + (k + 1) = (C + 1) + k from by ring]
    step fm
    exact ih A (C + 1) F

theorem r2_chain : ∀ k, ∀ A B E,
    ⟨A, B, 0, k, E, k⟩ [fm]⊢* ⟨A + k, B + 2 * k, 0, 0, E, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · exists 0
  · step fm
    rw [show A + (k + 1) = (A + 1) + k from by ring,
        show B + 2 * (k + 1) = (B + 2) + 2 * k from by ring]
    exact ih (A + 1) (B + 2) E

theorem b_drain : ∀ k, ∀ A E F,
    ⟨A, k, 0, 0, E, F⟩ [fm]⊢* ⟨A + k, 0, 0, 0, E, F + k⟩ := by
  intro k; induction' k with k ih <;> intro A E F
  · exists 0
  · step fm
    rw [show A + (k + 1) = (A + 1) + k from by ring,
        show F + (k + 1) = (F + 1) + k from by ring]
    exact ih (A + 1) E (F + 1)

theorem middle : ∀ k, ∀ A D E,
    ⟨A, 2, k, D, E, k + D⟩ [fm]⊢* ⟨A + k + D, k + 2 + 2 * D, 0, 0, E + k, 0⟩ := by
  intro k; induction' k using Nat.strongRecOn with k ih; intro A D E
  rcases k with _ | _ | k
  · -- k = 0
    simp only [Nat.zero_add, Nat.add_zero]
    rw [show 0 + 2 + 2 * D = 2 + 2 * D from by ring]
    exact r2_chain D A 2 E
  · -- k = 1
    rw [show (1 : ℕ) + D = D + 1 from by ring]
    step fm
    rw [show A + 1 + D = A + (D + 1) from by ring,
        show 1 + 2 + 2 * D = 1 + 2 * (D + 1) from by ring,
        show E + 1 = E + 1 from rfl]
    exact r2_chain (D + 1) A 1 (E + 1)
  · -- k + 2
    rw [show k + 2 + D = k + (D + 2) from by ring]
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    rw [show k + 2 = (k + 1) + 1 from by ring]
    step fm
    step fm
    rw [show k + (D + 2) = (k + (D + 1)) + 1 from by ring]
    step fm
    -- Now state: ⟨A + 1, 2, k, D + 1, E + 2, k + (D + 1)⟩
    rw [show A + (k + 1 + 1) + D = (A + 1) + k + (D + 1) from by ring,
        show (k + 1 + 1) + 2 + 2 * D = k + 2 + 2 * (D + 1) from by ring,
        show E + (k + 1 + 1) = (E + 2) + k from by ring,
        show E + 1 + 1 = E + 2 from by ring]
    exact ih k (by omega) (A + 1) (D + 1) (E + 2)

theorem main_trans (n : ℕ) :
    ⟨n * n + 3 * n + 3, 0, 0, 0, n + 2, n + 2⟩ [fm]⊢⁺
    ⟨n * n + 5 * n + 7, 0, 0, 0, n + 3, n + 3⟩ := by
  have p1 : ⟨n * n + 3 * n + 3, 0, 0, 0, n + 2, n + 2⟩ [fm]⊢*
      ⟨n * n + 3 * n + 3, 0, n + 2, 0, 0, n + 2⟩ := by
    have h := e_to_c (n + 2) (n * n + 3 * n + 3) 0 (n + 2)
    simpa using h
  have p2 : ⟨n * n + 3 * n + 3, 0, n + 2, 0, 0, n + 2⟩ [fm]⊢*
      ⟨n * n + 3 * n + 3, 2, n + 1, 0, 2, n + 1⟩ := by
    rw [show n * n + 3 * n + 3 = (n * n + 3 * n + 2) + 1 from by ring,
        show n + 2 = (n + 1) + 1 from by ring]
    step fm
    step fm
    rw [show (n + 1) + 1 = (n + 1) + 1 from rfl]
    step fm
    ring_nf; finish
  have p3 : ⟨n * n + 3 * n + 3, 2, n + 1, 0, 2, n + 1⟩ [fm]⊢*
      ⟨n * n + 4 * n + 4, n + 3, 0, 0, n + 3, 0⟩ := by
    have h := middle (n + 1) (n * n + 3 * n + 3) 0 2
    rw [show n + 1 + 0 = n + 1 from by ring,
        show n * n + 3 * n + 3 + (n + 1) + 0 = n * n + 4 * n + 4 from by ring,
        show n + 1 + 2 + 2 * 0 = n + 3 from by ring,
        show 2 + (n + 1) = n + 3 from by ring] at h
    exact h
  have p4 : ⟨n * n + 4 * n + 4, n + 3, 0, 0, n + 3, 0⟩ [fm]⊢*
      ⟨n * n + 5 * n + 7, 0, 0, 0, n + 3, n + 3⟩ := by
    have h := b_drain (n + 3) (n * n + 4 * n + 4) (n + 3) 0
    rw [show n * n + 4 * n + 4 + (n + 3) = n * n + 5 * n + 7 from by ring,
        show 0 + (n + 3) = n + 3 from by ring] at h
    exact h
  have p_all := stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4
  exact stepStar_stepPlus p_all (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 2, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n * n + 3 * n + 3, 0, 0, 0, n + 2, n + 2⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  rw [show (n + 1) * (n + 1) + 3 * (n + 1) + 3 = n * n + 5 * n + 7 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1608
