import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1661

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · simp; exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    rw [show C + (k + 1) = (C + 1) + k from by ring]
    exact ih A (C + 1)

theorem r2_chain : ∀ k, ∀ A D E,
    ⟨A, k, 0, D, E⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · simp; exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (A + 2) D E)
    ring_nf; finish

theorem interleave : ∀ M, ∀ A B C D E,
    2 * C + D = M →
    ⟨A + C, B + 1, C, D, E⟩ [fm]⊢* ⟨A + 2 * C + 2 * B + 2 + 3 * D, 0, 0, 0, E + C⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B C D E hM
  rcases C with _ | C
  · rcases D with _ | D
    · simp
      have := r2_chain (B + 1) A 0 E
      rw [show A + 2 * (B + 1) = A + 2 * B + 2 from by ring] at this
      exact this
    · have phase1 := r2_chain (B + 1) A (D + 1) E
      rw [show A + 2 * (B + 1) = A + 2 * B + 2 from by ring] at phase1
      apply stepStar_trans phase1
      rw [show A + 2 * B + 2 = (A + 2 * B + 1) + 1 from by ring,
          show D + 1 = D + 1 from rfl]
      step fm
      have hlt : 2 * 0 + D < M := by omega
      have h := ih (2 * 0 + D) hlt (A + 2 * B + 1) 1 0 D E rfl
      rw [show (A + 2 * B + 1) + 2 * 0 + 2 * 1 + 2 + 3 * D =
            A + 2 * 0 + 2 * B + 2 + 3 * (D + 1) from by ring,
          show E + 0 = E + 0 from rfl,
          show (A + 2 * B + 1) + 0 = A + 2 * B + 1 from by ring] at h
      exact h
  · rcases B with _ | B
    · show ⟨A + (C + 1), 0 + 1, C + 1, D, E⟩ [fm]⊢*
        ⟨A + 2 * (C + 1) + 2 * 0 + 2 + 3 * D, 0, 0, 0, E + (C + 1)⟩
      rw [show (C + 1 : ℕ) = C + 1 from rfl]
      step fm
      rw [show A + (C + 1) = (A + C) + 1 from by ring,
          show D + 1 = D + 1 from rfl]
      step fm
      have hlt : 2 * C + D < M := by omega
      have h := ih (2 * C + D) hlt A 1 C D (E + 1) rfl
      rw [show A + 2 * C + 2 * 1 + 2 + 3 * D =
            A + 2 * (C + 1) + 2 * 0 + 2 + 3 * D from by ring,
          show (E + 1) + C = E + (C + 1) from by ring,
          show A + C = A + C from rfl] at h
      exact h
    · show ⟨A + (C + 1), (B + 1) + 1, C + 1, D, E⟩ [fm]⊢*
        ⟨A + 2 * (C + 1) + 2 * (B + 1) + 2 + 3 * D, 0, 0, 0, E + (C + 1)⟩
      rw [show (C + 1 : ℕ) = C + 1 from rfl]
      step fm
      have hlt : 2 * C + (D + 1) < M := by omega
      have h := ih (2 * C + (D + 1)) hlt (A + 1) B C (D + 1) (E + 1) rfl
      rw [show (A + 1) + 2 * C + 2 * B + 2 + 3 * (D + 1) =
            A + 2 * (C + 1) + 2 * (B + 1) + 2 + 3 * D from by ring,
          show (E + 1) + C = E + (C + 1) from by ring,
          show (A + 1) + C = A + (C + 1) from by ring] at h
      exact h

theorem main_trans (a n : ℕ) :
    ⟨a + 2 * n + 5, 0, 2 * n + 4, 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * n + 10, 0, 2 * n + 6, 0, 0⟩ := by
  have p1 : ⟨a + 2 * n + 5, 0, 2 * n + 4, 0, 0⟩ [fm]⊢⁺
      ⟨a + 2 * n + 4, 1, 2 * n + 4, 0, 2⟩ := by
    rw [show a + 2 * n + 5 = (a + 2 * n + 4) + 1 from by ring,
        show 2 * n + 4 = 0 + (2 * n + 4) from by ring]
    step fm; finish
  have p2 : ⟨a + 2 * n + 4, 1, 2 * n + 4, 0, 2⟩ [fm]⊢*
      ⟨a + 4 * n + 10, 0, 0, 0, 2 * n + 6⟩ := by
    have h := interleave (2 * (2 * n + 4) + 0) a 0 (2 * n + 4) 0 2 (by ring)
    rw [show a + 2 * (2 * n + 4) + 2 * 0 + 2 + 3 * 0 = a + 4 * n + 10 from by ring,
        show 2 + (2 * n + 4) = 2 * n + 6 from by ring,
        show a + (2 * n + 4) = a + 2 * n + 4 from by ring] at h
    exact h
  have p3 : ⟨a + 4 * n + 10, 0, 0, 0, 2 * n + 6⟩ [fm]⊢*
      ⟨a + 4 * n + 10, 0, 2 * n + 6, 0, 0⟩ := by
    have h := r4_chain (2 * n + 6) (a + 4 * n + 10) 0
    rw [show 0 + (2 * n + 6) = 2 * n + 6 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus p1 (stepStar_trans p2 p3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 4, 0, 0⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a + 2 * n + 5, 0, 2 * n + 4, 0, 0⟩) ⟨0, 0⟩
  intro ⟨a, n⟩
  refine ⟨⟨a + 2 * n + 3, n + 1⟩, ?_⟩
  show ⟨a + 2 * n + 5, 0, 2 * n + 4, 0, 0⟩ [fm]⊢⁺
    ⟨(a + 2 * n + 3) + 2 * (n + 1) + 5, 0, 2 * (n + 1) + 4, 0, 0⟩
  rw [show (a + 2 * n + 3) + 2 * (n + 1) + 5 = a + 4 * n + 10 from by ring,
      show 2 * (n + 1) + 4 = 2 * n + 6 from by ring]
  exact main_trans a n

end Sz22_2003_unofficial_1661
