import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1610

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem d_to_c : ∀ k c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- (R3, R1, R1) chain: k rounds
-- From (A+k, 0, C+2k+1, D, E+1) to (A, 0, C+1, D+2k, E+k+1)
theorem r311_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C + 2 * k + 1, D, E + 1⟩ [fm]⊢* ⟨A, 0, C + 1, D + 2 * k, E + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · -- Source: (A + (k+1), 0, C + 2*(k+1) + 1, D, E + 1)
    -- = (A + k + 1, 0, C + 2*k + 3, D, E + 1)
    rw [show A + (k + 1) = A + k + 1 from by ring,
        show C + 2 * (k + 1) + 1 = (C + 2 * k + 1) + 2 from by ring]
    -- R3: (A+k+1, 0, ..., D, E+1) -> (A+k, 2, ..., D, E)
    rw [show (C + 2 * k + 1 + 2 : ℕ) = (C + 2 * k + 2) + 1 from by ring]
    step fm
    -- R1: (A+k, 2, C+2k+2+1, D, E) -> (A+k, 1, C+2k+2, D+1, E+1)
    -- Actually after step fm the c is still C+2k+2+1 and we get (A+k, 1, C+2k+2, D+1, E+1)
    -- wait, R1: (a, b+1, c+1, d, e) -> (a, b, c, d+1, e+1)
    -- so (A+k, 2, (C+2k+2)+1, D, E) = (A+k, 1+1, (C+2k+2)+1, D, E) -> (A+k, 1, C+2k+2, D+1, E+1)
    -- Then R1 again: (A+k, 1, C+2k+2, D+1, E+1) = (A+k, 0+1, (C+2k+1)+1, D+1, E+1) -> (A+k, 0, C+2k+1, D+2, E+2)
    rw [show (C + 2 * k + 2 : ℕ) = (C + 2 * k + 1) + 1 from by ring]
    step fm
    step fm
    -- Now at: (A+k, 0, C+2k+1, D+1+1, E+1+1)
    -- Need to reach: (A, 0, C+1, D+2(k+1), E+(k+1)+1)
    -- ih with D' = D+2, E' = E+1:
    -- (A+k, 0, C+2k+1, D+2, (E+1)+1) ⊢* (A, 0, C+1, D+2+2k, (E+1)+k+1)
    rw [show D + 2 * (k + 1) = (D + 1 + 1) + 2 * k from by ring,
        show E + (k + 1) + 1 = (E + 1) + k + 1 from by ring,
        show (E + 1 + 1 : ℕ) = (E + 1) + 1 from by ring]
    exact ih A C (D + 1 + 1) (E + 1)

-- (R3, R2, R2) chain: k rounds
-- From (A+1, 0, 0, D, k+1) to (A+3k+4, 0, 0, D+4k+4, 0)
theorem r322_chain : ∀ k, ∀ A D,
    ⟨A + 1, 0, 0, D, k + 1⟩ [fm]⊢* ⟨A + 3 * k + 4, 0, 0, D + 4 * k + 4, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · -- R3: (A+1, 0, 0, D, 1) -> (A, 2, 0, D, 0)
    -- R2: (A, 2, 0, D, 0) -> (A+2, 1, 0, D+2, 0)
    -- R2: (A+2, 1, 0, D+2, 0) -> (A+4, 0, 0, D+4, 0)
    step fm; step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = k + 1 + 1 from rfl]
    -- R3: (A+1, 0, 0, D, k+2) -> (A, 2, 0, D, k+1)
    -- R2: (A, 2, 0, D, k+1) -> (A+2, 1, 0, D+2, k+1)
    -- R2: (A+2, 1, 0, D+2, k+1) -> (A+4, 0, 0, D+4, k+1)
    rw [show (k + 1 + 1 : ℕ) = k + 1 + 1 from rfl]
    step fm; step fm; step fm
    -- Now at (A+2+2, 0, 0, D+2+2, k+1)
    -- Need ih: ((A+3)+1, 0, 0, D+4, k+1) ⊢* ((A+3)+3k+4, 0, 0, (D+4)+4k+4, 0)
    rw [show A + 3 * (k + 1) + 4 = (A + 3) + 3 * k + 4 from by ring,
        show D + 4 * (k + 1) + 4 = (D + 4) + 4 * k + 4 from by ring]
    have : (A + 2 + 2, 0, 0, D + 2 + 2, k + 1) = ((A + 3) + 1, 0, 0, D + 4, k + 1) := by ring_nf
    rw [this]
    exact ih (A + 3) (D + 4)

theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, 2 * n, 0⟩ [fm]⊢⁺ ⟨3 * n + 2, 0, 0, 6 * n + 2, 0⟩ := by
  rcases n with _ | n'
  · step fm; step fm; finish
  · -- n = n' + 1 >= 1
    -- Phase 1: d -> c
    have p1 : ⟨n' + 2, 0, 0, 2 * n' + 2, 0⟩ [fm]⊢* ⟨n' + 2, 0, 2 * n' + 2, 0, 0⟩ := by
      have := d_to_c (a := n' + 2) (2 * n' + 2) 0; simpa using this
    -- Phase 2: R5 then R1
    have p2 : ⟨n' + 2, 0, 2 * n' + 2, 0, 0⟩ [fm]⊢* ⟨n' + 1, 0, 2 * n' + 1, 1, 1⟩ := by
      rw [show (n' + 2 : ℕ) = (n' + 1) + 1 from by ring,
          show (2 * n' + 2 : ℕ) = (2 * n' + 1) + 1 from by ring]
      step fm
      rw [show (2 * n' + 1 + 1 : ℕ) = (2 * n' + 1) + 1 from by ring]
      step fm; finish
    -- Phase 3: (R3, R1, R1) x n' rounds
    -- From (n'+1, 0, 2n'+1, 1, 1) to (1, 0, 1, 2n'+1, n'+1)
    -- Use r311_chain with k=n', A=1, C=0, D=1, E=0:
    --   (1+n', 0, 0+2n'+1, 1, 0+1) ⊢* (1, 0, 0+1, 1+2n', 0+n'+1)
    have p3 : ⟨n' + 1, 0, 2 * n' + 1, 1, 1⟩ [fm]⊢* ⟨1, 0, 1, 2 * n' + 1, n' + 1⟩ := by
      have h := r311_chain n' 1 0 1 0
      rw [show 1 + n' = n' + 1 from by ring,
          show 0 + 2 * n' + 1 = 2 * n' + 1 from by ring,
          show 1 + 2 * n' = 2 * n' + 1 from by ring,
          show (0 + 1 : ℕ) = 1 from rfl,
          show 0 + n' + 1 = n' + 1 from by ring] at h
      exact h
    -- Phase 4: final R3, R1
    have p4 : ⟨1, 0, 1, 2 * n' + 1, n' + 1⟩ [fm]⊢* ⟨0, 1, 0, 2 * n' + 2, n' + 1⟩ := by
      step fm; step fm; finish
    -- Phase 5: R2
    have p5 : ⟨0, 1, 0, 2 * n' + 2, n' + 1⟩ [fm]⊢* ⟨2, 0, 0, 2 * n' + 4, n' + 1⟩ := by
      step fm
      show (0 + 2, 0, 0, 2 * n' + 2 + 2, n' + 1) [fm]⊢* (2, 0, 0, 2 * n' + 4, n' + 1)
      ring_nf; finish
    -- Phase 6: (R3, R2, R2) x n' rounds
    have p6 : ⟨2, 0, 0, 2 * n' + 4, n' + 1⟩ [fm]⊢* ⟨3 * n' + 5, 0, 0, 6 * n' + 8, 0⟩ := by
      show (1 + 1, 0, 0, 2 * n' + 4, n' + 1) [fm]⊢* (3 * n' + 5, 0, 0, 6 * n' + 8, 0)
      have h := r322_chain n' 1 (2 * n' + 4)
      rw [show 1 + 3 * n' + 4 = 3 * n' + 5 from by ring,
          show 2 * n' + 4 + 4 * n' + 4 = 6 * n' + 8 from by ring] at h
      exact h
    rw [show 2 * (n' + 1) = 2 * n' + 2 from by ring,
        show 3 * (n' + 1) + 2 = 3 * n' + 5 from by ring,
        show 6 * (n' + 1) + 2 = 6 * n' + 8 from by ring]
    have pall : ⟨n' + 2, 0, 0, 2 * n' + 2, 0⟩ [fm]⊢* ⟨3 * n' + 5, 0, 0, 6 * n' + 8, 0⟩ :=
      stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 p6))))
    exact stepStar_stepPlus pall (by simp [Q]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 2 * n, 0⟩) 0
  intro n
  refine ⟨3 * n + 1, ?_⟩
  show ⟨n + 1, 0, 0, 2 * n, 0⟩ [fm]⊢⁺ ⟨3 * n + 1 + 1, 0, 0, 2 * (3 * n + 1), 0⟩
  rw [show 3 * n + 1 + 1 = 3 * n + 2 from by ring,
      show 2 * (3 * n + 1) = 6 * n + 2 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1610
