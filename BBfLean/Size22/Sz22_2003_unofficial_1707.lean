import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1707: [77/15, 9/91, 26/3, 5/11, 455/2]

Vector representation:
```
 0 -1 -1  1  1  0
 0  2  0 -1  0 -1
 1 -1  0  0  0  1
 0  0  1  0 -1  0
-1  0  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1707

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f+1⟩
  | _ => none

-- R4 chain: transfer e to c
theorem e_to_c : ∀ k, ∀ A C F,
    ⟨A, 0, C, 0, k, F⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro A C F
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1) F)
    rw [show C + 1 + k = C + (k + 1) from by ring]; finish

-- R3 chain: transfer b to a and f
theorem r3_chain : ∀ k, ∀ A E F,
    ⟨A, k, 0, 0, E, F⟩ [fm]⊢* ⟨A + k, 0, 0, 0, E, F + k⟩ := by
  intro k; induction' k with k ih <;> intro A E F
  · exists 0
  · step fm
    apply stepStar_trans (ih (A + 1) E (F + 1))
    rw [show A + 1 + k = A + (k + 1) from by ring,
        show F + 1 + k = F + (k + 1) from by ring]; finish

-- Combined drain: strong induction on 2*C+D.
-- Drains c and d using interleaved R1 and R2.
theorem combined_drain : ∀ M, ∀ X B C D E F, 2 * C + D = M →
    (B + D ≥ 1 ∨ C = 0) →
    ⟨X, B, C, D, E, F + C + D⟩ [fm]⊢* ⟨X, B + C + 2 * D, 0, 0, E + C, F⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro X B C D E F hM hpre
  rcases C with _ | C
  · rcases D with _ | D
    · simp; exists 0
    · rw [show F + 0 + (D + 1) = (F + 0 + D) + 1 from by ring]
      step fm
      have := ih (2 * 0 + D) (by omega) X (B + 2) 0 D E F (by ring) (by left; omega)
      rw [show B + 2 + 0 + 2 * D = B + 0 + 2 * (D + 1) from by ring,
          show E + 0 = E + 0 from rfl] at this
      exact this
  · rcases D with _ | D
    · rcases B with _ | B
      · simp at hpre
      · step fm
        have := ih (2 * C + 1) (by omega) X B C 1 (E + 1) F (by ring) (by left; omega)
        rw [show B + C + 2 * 1 = (B + 1) + (C + 1) + 2 * 0 from by ring,
            show E + 1 + C = E + (C + 1) from by ring,
            show F + C + 1 = F + (C + 1) + 0 from by ring] at this
        exact this
    · rcases B with _ | B
      · rw [show F + (C + 1) + (D + 1) = (F + (C + 1) + D) + 1 from by ring]
        step fm
        have := ih (2 * (C + 1) + D) (by omega) X 2 (C + 1) D E F (by ring)
          (by left; omega)
        rw [show 2 + (C + 1) + 2 * D = 0 + (C + 1) + 2 * (D + 1) from by ring,
            show E + (C + 1) = E + (C + 1) from rfl] at this
        exact this
      · step fm
        have := ih (2 * C + (D + 2)) (by omega) X B C (D + 2) (E + 1) F (by ring)
          (by left; omega)
        rw [show B + C + 2 * (D + 2) = (B + 1) + (C + 1) + 2 * (D + 1) from by ring,
            show E + 1 + C = E + (C + 1) from by ring,
            show F + C + (D + 2) = F + (C + 1) + (D + 1) from by ring] at this
        exact this

-- Main transition: (A+1, 0, C+1, 0, 0, 2*C+2) ⊢⁺ (A+C+4, 0, C+2, 0, 0, 2*C+4)
theorem main_trans (A C : ℕ) :
    ⟨A + 1, 0, C + 1, 0, 0, 2 * C + 2⟩ [fm]⊢⁺
    ⟨A + C + 4, 0, C + 2, 0, 0, 2 * C + 4⟩ := by
  -- Phase 1: R5 fires: (A+1, 0, C+1, 0, 0, 2C+2) -> (A, 0, C+2, 1, 0, 2C+3)
  have p1 : ⟨A + 1, 0, C + 1, 0, 0, 2 * C + 2⟩ [fm]⊢⁺
      ⟨A, 0, C + 2, 1, 0, 2 * C + 3⟩ := by
    step fm; finish
  -- Phase 2: R2 fires: (A, 0, C+2, 1, 0, 2C+3) -> (A, 2, C+2, 0, 0, 2C+2)
  have p2 : ⟨A, 0, C + 2, 1, 0, 2 * C + 3⟩ [fm]⊢⁺
      ⟨A, 2, C + 2, 0, 0, 2 * C + 2⟩ := by
    step fm; finish
  -- Phase 3: Combined drain of c+2 via interleaved R1/R2
  -- (A, 2, C+2, 0, 0, 2C+2) -> (A, C+4, 0, 0, C+2, C)
  have p3 : ⟨A, 2, C + 2, 0, 0, 2 * C + 2⟩ [fm]⊢*
      ⟨A, C + 4, 0, 0, C + 2, C⟩ := by
    rw [show 2 * C + 2 = C + (C + 2) + 0 from by ring]
    have := combined_drain (2 * (C + 2) + 0) A 2 (C + 2) 0 0 C (by ring)
      (by left; omega)
    rw [show 2 + (C + 2) + 2 * 0 = C + 4 from by ring,
        show 0 + (C + 2) = C + 2 from by ring] at this
    exact this
  -- Phase 4: R3 chain: (A, C+4, 0, 0, C+2, C) -> (A+C+4, 0, 0, 0, C+2, 2C+4)
  have p4 : ⟨A, C + 4, 0, 0, C + 2, C⟩ [fm]⊢*
      ⟨A + C + 4, 0, 0, 0, C + 2, 2 * C + 4⟩ := by
    have := r3_chain (C + 4) A (C + 2) C
    rw [show A + (C + 4) = A + C + 4 from by ring,
        show C + (C + 4) = 2 * C + 4 from by ring] at this
    exact this
  -- Phase 5: R4 chain: (A+C+4, 0, 0, 0, C+2, 2C+4) -> (A+C+4, 0, C+2, 0, 0, 2C+4)
  have p5 : ⟨A + C + 4, 0, 0, 0, C + 2, 2 * C + 4⟩ [fm]⊢*
      ⟨A + C + 4, 0, C + 2, 0, 0, 2 * C + 4⟩ := by
    have := e_to_c (C + 2) (A + C + 4) 0 (2 * C + 4)
    simp only [Nat.zero_add] at this; exact this
  -- Compose all phases
  exact stepPlus_stepStar_stepPlus
    (stepPlus_stepStar_stepPlus p1
      (stepPlus_stepStar p2))
    (stepStar_trans p3 (stepStar_trans p4 p5))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 1, 0, 0, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, C⟩ ↦ ⟨A + 1, 0, C + 1, 0, 0, 2 * C + 2⟩) ⟨2, 0⟩
  intro ⟨A, C⟩
  refine ⟨⟨A + C + 3, C + 1⟩, ?_⟩
  show ⟨A + 1, 0, C + 1, 0, 0, 2 * C + 2⟩ [fm]⊢⁺
    ⟨A + C + 3 + 1, 0, C + 1 + 1, 0, 0, 2 * (C + 1) + 2⟩
  rw [show A + C + 3 + 1 = A + C + 4 from by ring,
      show C + 1 + 1 = C + 2 from by ring,
      show 2 * (C + 1) + 2 = 2 * C + 4 from by ring]
  exact main_trans A C

end Sz22_2003_unofficial_1707
