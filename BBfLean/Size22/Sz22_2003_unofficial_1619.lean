import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1619: [77/15, 2/3, 9/14, 5/11, 2541/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  0  0
-1  2  0 -1  0
 0  0  1  0 -1
-1  1  0  1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1619

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+2⟩
  | _ => none

-- R4 chain: transfer e to c
theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  step fm; apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- R3/R2/R2 drain: each round a+=1, d-=1
theorem r3r2r2_drain : ∀ k, ∀ A E, ⟨A + 1, 0, 0, k, E⟩ [fm]⊢* ⟨A + k + 1, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  step fm; step fm; step fm
  rw [show A + (k + 1) + 1 = (A + 1) + k + 1 from by ring]
  exact ih (A + 1) E

-- Interleaved R3/R1/R1 chain
theorem r3r1r1_chain : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C + 2 * k, D + 1, E⟩ [fm]⊢* ⟨A, 0, C, D + k + 1, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show C + 2 * (k + 1) = (C + 2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show D + (k + 1) + 1 = (D + 1) + k + 1 from by ring,
      show E + 2 * (k + 1) = (E + 2) + 2 * k from by ring]
  exact ih A C (D + 1) (E + 2)

-- Main transition: (n+2, 0, 0, 0, 2n+2) ⊢⁺ (n+3, 0, 0, 0, 2n+4)
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
  have p1 : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢* ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ := by
    have := e_to_c (a := n + 2) (2 * n + 2) 0; simpa using this
  have p2 : ⟨n + 2, 0, 2 * n + 2, 0, 0⟩ [fm]⊢* ⟨n + 1, 1, 2 * n + 2, 1, 2⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]; step fm; finish
  have p3a : ⟨n + 1, 1, 2 * n + 2, 1, 2⟩ [fm]⊢* ⟨n + 1, 0, 2 * n + 1, 2, 3⟩ := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]; step fm; finish
  have p3b : ⟨n + 1, 0, 2 * n + 1, 2, 3⟩ [fm]⊢* ⟨1, 0, 1, n + 2, 2 * n + 3⟩ := by
    rw [show n + 1 = 1 + n from by ring,
        show 2 * n + 1 = 1 + 2 * n from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show n + 2 = 1 + n + 1 from by ring,
        show 2 * n + 3 = 3 + 2 * n from by ring]
    exact r3r1r1_chain n 1 1 1 3
  have p3c : ⟨1, 0, 1, n + 2, 2 * n + 3⟩ [fm]⊢* ⟨1, 0, 0, n + 2, 2 * n + 4⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show n + 2 = (n + 1) + 1 from by ring]
    step fm; step fm; step fm; ring_nf; finish
  have p4 : ⟨1, 0, 0, n + 2, 2 * n + 4⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show n + 3 = 0 + (n + 2) + 1 from by ring]
    exact r3r2r2_drain (n + 2) 0 (2 * n + 4)
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus (stepStar_stepPlus p2 (by unfold Q; simp))
      (stepStar_trans (stepStar_trans (stepStar_trans p3a p3b) p3c) p4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩)
  · unfold c₀; execute fm 5
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨n + 1 + 2, 0, 0, 0, 2 * (n + 1) + 2⟩
  rw [show n + 1 + 2 = n + 3 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1619
