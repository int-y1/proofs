import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1702: [77/15, 9/91, 26/3, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  1  0
 0  2  0 -1  0 -1
 1 -1  0  0  0  1
 0  0  1  0 -1  0
-1  1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1702

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d+1, e+1, f⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C F,
    ⟨A, 0, C, 0, k, F⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro A C F
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1) F)
    rw [show C + 1 + k = C + (k + 1) from by ring]; finish

theorem r3_chain : ∀ k, ∀ A E F,
    ⟨A, k, 0, 0, E, F⟩ [fm]⊢* ⟨A + k, 0, 0, 0, E, F + k⟩ := by
  intro k; induction' k with k ih <;> intro A E F
  · exists 0
  · step fm
    apply stepStar_trans (ih (A + 1) E (F + 1))
    rw [show A + 1 + k = A + (k + 1) from by ring,
        show F + 1 + k = F + (k + 1) from by ring]; finish

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

theorem main_trans (A E : ℕ) :
    ⟨A + 1, 0, 0, 0, E + 1, 2 * E + 2⟩ [fm]⊢⁺
    ⟨A + E + 4, 0, 0, 0, E + 2, 2 * E + 4⟩ := by
  -- Phase 1: R4 × (E+1): drain e to c
  have p1 : ⟨A + 1, 0, 0, 0, E + 1, 2 * E + 2⟩ [fm]⊢*
      ⟨A + 1, 0, E + 1, 0, 0, 2 * E + 2⟩ := by
    have := e_to_c (E + 1) (A + 1) 0 (2 * E + 2)
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5 (a ≥ 1, b=0, e=0)
  have p2 : ⟨A + 1, 0, E + 1, 0, 0, 2 * E + 2⟩ [fm]⊢⁺
      ⟨A, 1, E + 1, 1, 1, 2 * E + 2⟩ := by
    rw [show A + 1 = A + 1 from rfl]
    step fm; finish
  -- Phase 3: R1 (b=1 ≥ 1, c=E+1 ≥ 1)
  have p3 : ⟨A, 1, E + 1, 1, 1, 2 * E + 2⟩ [fm]⊢*
      ⟨A, 0, E, 2, 2, 2 * E + 2⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show E + 1 = E + 1 from rfl]
    step fm; ring_nf; finish
  -- Phase 4: Combined drain of c=E, d=2
  have p4 : ⟨A, 0, E, 2, 2, 2 * E + 2⟩ [fm]⊢*
      ⟨A, E + 4, 0, 0, E + 2, E⟩ := by
    rw [show 2 * E + 2 = E + E + 2 from by ring]
    have := combined_drain (2 * E + 2) A 0 E 2 2 E (by ring) (by left; omega)
    rw [show 0 + E + 2 * 2 = E + 4 from by ring,
        show 2 + E = E + 2 from by ring] at this
    exact this
  -- Phase 5: R3 × (E+4): drain b to a and f
  have p5 : ⟨A, E + 4, 0, 0, E + 2, E⟩ [fm]⊢*
      ⟨A + E + 4, 0, 0, 0, E + 2, 2 * E + 4⟩ := by
    have := r3_chain (E + 4) A (E + 2) E
    rw [show A + (E + 4) = A + E + 4 from by ring,
        show E + (E + 4) = 2 * E + 4 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3 (stepStar_trans p4 p5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, E⟩ ↦ ⟨A + 1, 0, 0, 0, E + 1, 2 * E + 2⟩) ⟨2, 0⟩
  intro ⟨A, E⟩
  refine ⟨⟨A + E + 3, E + 1⟩, ?_⟩
  show ⟨A + 1, 0, 0, 0, E + 1, 2 * E + 2⟩ [fm]⊢⁺
    ⟨A + E + 3 + 1, 0, 0, 0, E + 1 + 1, 2 * (E + 1) + 2⟩
  rw [show A + E + 3 + 1 = A + E + 4 from by ring,
      show E + 1 + 1 = E + 2 from by ring,
      show 2 * (E + 1) + 2 = 2 * E + 4 from by ring]
  exact main_trans A E

end Sz22_2003_unofficial_1702
