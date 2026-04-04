import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1615: [77/15, 2/3, 9/14, 5/11, 1089/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  0  0
-1  2  0 -1  0
 0  0  1  0 -1
-1  2  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1615

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | _ => none

-- R4 transfer: e to c
theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · step fm; apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- R1R1R3 chain: k rounds of (R1, R1, R3)
theorem r1r1r3_chain : ∀ k, ∀ A C D E,
    ⟨A + k + 1, 2, C + 2 * k + 2, D, E⟩ [fm]⊢* ⟨A + 1, 2, C + 2, D + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  · rw [show A + (k + 1) + 1 = (A + k + 1) + 1 from by ring,
        show C + 2 * (k + 1) + 2 = (C + 2 * k + 2) + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show D + (k + 1) = (D + 1) + k from by ring,
        show E + 2 * (k + 1) = (E + 2) + 2 * k from by ring]
    exact ih A C (D + 1) (E + 2)

-- R3R2R2 drain: (A+1, 0, 0, k+1, E) -> (A+k+2, 0, 0, 0, E)
theorem r3r2r2_drain : ∀ k, ∀ A E,
    ⟨A + 1, 0, 0, k + 1, E⟩ [fm]⊢* ⟨A + k + 2, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show A + 1 + 1 = (A + 1) + 1 from by ring,
        show A + (k + 1) + 2 = (A + 1) + k + 2 from by ring]
    exact ih (A + 1) E

-- Main transition: (n+1, 0, 0, 0, 2n) ⊢⁺ (n+2, 0, 0, 0, 2n+2)
theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, 0, 2 * n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ := by
  rcases n with _ | n
  · -- n = 0: (1,0,0,0,0) -> R5 -> (0,2,0,0,2) -> R2 -> (1,1,0,0,2) -> R2 -> (2,0,0,0,2)
    step fm; step fm; step fm; finish
  · have p1 : ⟨n + 2, 0, 0, 0, 2 * (n + 1)⟩ [fm]⊢* ⟨n + 2, 0, 2 * (n + 1), 0, 0⟩ := by
      have := e_to_c (a := n + 2) (2 * (n + 1)) 0; simpa using this
    have p2 : ⟨n + 2, 0, 2 * (n + 1), 0, 0⟩ [fm]⊢* ⟨n + 1, 2, 2 * (n + 1), 0, 2⟩ := by
      rw [show n + 2 = (n + 1) + 1 from by ring]; step fm; finish
    have p3 : ⟨n + 1, 2, 2 * (n + 1), 0, 2⟩ [fm]⊢* ⟨1, 2, 2, n, 2 * n + 2⟩ := by
      have h := r1r1r3_chain n 0 0 0 2
      rw [show 0 + n + 1 = n + 1 from by omega,
          show 0 + 2 * n + 2 = 2 * (n + 1) from by ring,
          show 0 + 1 = 1 from by omega,
          show 0 + 2 = 2 from by omega,
          show 0 + n = n from by omega,
          show 2 + 2 * n = 2 * n + 2 from by ring] at h
      exact h
    have p4 : ⟨1, 2, 2, n, 2 * n + 2⟩ [fm]⊢* ⟨1, 0, 0, n + 2, 2 * n + 4⟩ := by
      step fm; step fm; ring_nf; finish
    have p5 : ⟨1, 0, 0, n + 2, 2 * n + 4⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
      rw [show (1 : ℕ) = 0 + 1 from by omega,
          show n + 2 = (n + 1) + 1 from by ring,
          show n + 3 = 0 + (n + 1) + 2 from by omega]
      exact r3r2r2_drain (n + 1) 0 (2 * n + 4)
    have p_all : ⟨n + 2, 0, 0, 0, 2 * (n + 1)⟩ [fm]⊢*
        ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ :=
      stepStar_trans (stepStar_trans (stepStar_trans (stepStar_trans p1 p2) p3) p4) p5
    rw [show n + 1 + 1 = n + 2 from by ring,
        show n + 1 + 2 = n + 3 from by ring,
        show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
    exact stepStar_stepPlus p_all (by intro h; simp [Q] at h)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, 2 * n⟩) 0
  intro n; exists n + 1
  rw [show (n + 1) + 1 = n + 2 from by ring,
      show 2 * (n + 1) = 2 * n + 2 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1615
