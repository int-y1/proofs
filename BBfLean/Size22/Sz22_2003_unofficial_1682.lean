import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1682

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · simp; exists 0
  · rw [show C + 2 * (k + 1) = (C + 2) + 2 * k from by ring]
    step fm
    exact ih A (C + 2)

theorem r3_chain : ∀ k, ∀ A E,
    ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (A + 2) E)
    rw [show A + 2 + 2 * k = A + 2 * (k + 1) from by ring]; finish

theorem r2r1r1_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C + 2 * k, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + 1 + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A C (D + 1) (E + 2))
    rw [show D + 1 + 1 + k = D + 1 + (k + 1) from by ring,
        show E + 2 + 2 * k = E + 2 * (k + 1) from by ring]; finish

theorem drain : ∀ M, ∀ A B D E, 3 * D + B = M →
    ⟨A, B + 1, 0, D, E⟩ [fm]⊢* ⟨A + 2 * B + 2 + 3 * D, 0, 0, 0, E⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B D E hM
  rcases D with _ | D
  · rcases B with _ | B
    · step fm; ring_nf; finish
    · rw [show (B + 1) + 1 = (B + 1) + 1 from rfl]
      step fm
      have := ih (3 * 0 + B) (by omega) (A + 2) B 0 E rfl
      rw [show (A + 2) + 2 * B + 2 + 3 * 0 = A + 2 * (B + 1) + 2 + 3 * 0 from by ring] at this
      exact this
  · rcases A with _ | A
    · rcases B with _ | B
      · step fm
        rw [show D + 1 = D + 1 from rfl]
        step fm
        have := ih (3 * D + 1) (by omega) 1 1 D E rfl
        rw [show 1 + 2 * 1 + 2 + 3 * D = 0 + 2 * 0 + 2 + 3 * (D + 1) from by ring] at this
        exact this
      · rw [show (B + 1) + 1 = (B + 1) + 1 from rfl]
        step fm
        have := ih (3 * (D + 1) + B) (by omega) 2 B (D + 1) E rfl
        rw [show 2 + 2 * B + 2 + 3 * (D + 1) = 0 + 2 * (B + 1) + 2 + 3 * (D + 1) from by ring] at this
        exact this
    · rw [show A + 1 = A + 1 from rfl, show D + 1 = D + 1 from rfl]
      step fm
      have := ih (3 * D + (B + 2)) (by omega) A (B + 2) D E rfl
      rw [show A + 2 * (B + 2) + 2 + 3 * D = (A + 1) + 2 * B + 2 + 3 * (D + 1) from by ring] at this
      exact this

theorem main_trans (a n : ℕ) :
    ⟨a + n + 2, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨a + 3 * n + 5, 0, 0, 0, 2 * n + 3⟩ := by
  have p1 : ⟨a + n + 2, 0, 0, 0, n + 1⟩ [fm]⊢* ⟨a + n + 2, 0, 2 * n + 2, 0, 0⟩ := by
    have := r4_chain (n + 1) (a + n + 2) 0
    simp only [Nat.zero_add] at this
    rw [show 2 * n + 2 = 2 * (n + 1) from by ring]
    exact this
  have p2 : ⟨a + n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + n + 1, 1, 2 * n + 2, 0, 1⟩ := by
    rw [show a + n + 2 = (a + n + 1) + 1 from by ring]
    step fm; finish
  have p3 : ⟨a + n + 1, 1, 2 * n + 2, 0, 1⟩ [fm]⊢* ⟨a + n + 1, 0, 2 * n + 1, 1, 2⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
    step fm; ring_nf; finish
  have p4 : ⟨a + n + 1, 0, 2 * n + 1, 1, 2⟩ [fm]⊢* ⟨a + 1, 0, 1, n + 1, 2 * n + 2⟩ := by
    rw [show a + n + 1 = (a + 1) + n from by ring,
        show 2 * n + 1 = 1 + 2 * n from by ring]
    have := r2r1r1_chain n (a + 1) 1 0 2
    rw [show 0 + 1 + n = n + 1 from by ring,
        show 2 + 2 * n = 2 * n + 2 from by ring] at this
    exact this
  have p5 : ⟨a + 1, 0, 1, n + 1, 2 * n + 2⟩ [fm]⊢* ⟨a, 2, 1, n, 2 * n + 2⟩ := by
    rw [show a + 1 = a + 1 from rfl, show n + 1 = n + 1 from rfl]
    step fm; ring_nf; finish
  have p6 : ⟨a, 2, 1, n, 2 * n + 2⟩ [fm]⊢* ⟨a, 1, 0, n + 1, 2 * n + 3⟩ := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
    step fm; ring_nf; finish
  have p7 : ⟨a, 1, 0, n + 1, 2 * n + 3⟩ [fm]⊢* ⟨a + 3 * n + 5, 0, 0, 0, 2 * n + 3⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    have := drain (3 * (n + 1) + 0) a 0 (n + 1) (2 * n + 3) (by ring)
    rw [show a + 2 * 0 + 2 + 3 * (n + 1) = a + 3 * n + 5 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 (stepStar_trans p6 p7)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a + n + 2, 0, 0, 0, n + 1⟩) ⟨0, 0⟩
  intro ⟨a, n⟩
  refine ⟨⟨a + n + 1, 2 * n + 2⟩, ?_⟩
  show ⟨a + n + 2, 0, 0, 0, n + 1⟩ [fm]⊢⁺
    ⟨(a + n + 1) + (2 * n + 2) + 2, 0, 0, 0, (2 * n + 2) + 1⟩
  rw [show (a + n + 1) + (2 * n + 2) + 2 = a + 3 * n + 5 from by ring,
      show (2 * n + 2) + 1 = 2 * n + 3 from by ring]
  exact main_trans a n

end Sz22_2003_unofficial_1682
