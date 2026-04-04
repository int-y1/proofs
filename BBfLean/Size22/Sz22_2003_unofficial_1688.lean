import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1688: [77/15, 9/14, 44/3, 5/11, 21/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 2 -1  0  0  1
 0  0  1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1688

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Phase 1: R4 fires k times, converting e to c
theorem r4_chain : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A C
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih A (C + 1))
    rw [show C + 1 + k = C + (k + 1) from by ring]; finish

-- Phase 5: R2 fires k times, converting (a,d) to (a-k, b+2k, d-k)
theorem r2_chain : ∀ k, ∀ A B E,
    ⟨A + k, B, 0, k, E⟩ [fm]⊢* ⟨A, B + 2 * k, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · simp; exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih A (B + 2) E)
    rw [show B + 2 + 2 * k = B + 2 * (k + 1) from by ring]; finish

-- Phase 6: R3 fires k times, converting b to a and e
theorem r3_chain : ∀ k, ∀ A E,
    ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + 2 * k, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (A + 2) (E + 1))
    rw [show A + 2 + 2 * k = A + 2 * (k + 1) from by ring,
        show E + 1 + k = E + (k + 1) from by ring]; finish

-- Phase 4: (R2, R1, R1) chain fires k times
-- From (A+k, 0, 2*k+C, D, E) to (A, 0, C, D+k, E+2*k)
-- Actually: from state (A+1+k, 0, E_val-1-2*...) pattern
-- Let me use the pattern: (A+k, 0, C+2*k, D+1, E) -> (A, 0, C, D+1+k, E+2*k)
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

-- Main transition: (2*m+F+3, 0, 0, 0, 2*m+1) ⊢⁺ (4*m+F+8, 0, 0, 0, 4*m+5)
theorem main_trans (F m : ℕ) :
    ⟨2 * m + F + 3, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺
    ⟨4 * m + F + 8, 0, 0, 0, 4 * m + 5⟩ := by
  -- Phase 1: R4 fires 2*m+1 times
  have p1 : ⟨2 * m + F + 3, 0, 0, 0, 2 * m + 1⟩ [fm]⊢*
      ⟨2 * m + F + 3, 0, 2 * m + 1, 0, 0⟩ := by
    have := r4_chain (2 * m + 1) (2 * m + F + 3) 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R5 fires once
  have p2 : ⟨2 * m + F + 3, 0, 2 * m + 1, 0, 0⟩ [fm]⊢⁺
      ⟨2 * m + F + 2, 1, 2 * m + 1, 1, 0⟩ := by
    rw [show 2 * m + F + 3 = (2 * m + F + 2) + 1 from by ring]
    step fm; finish
  -- Phase 3: R1 fires once
  have p3 : ⟨2 * m + F + 2, 1, 2 * m + 1, 1, 0⟩ [fm]⊢*
      ⟨2 * m + F + 2, 0, 2 * m, 2, 1⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, show 2 * m + 1 = (2 * m) + 1 from by ring]
    step fm; ring_nf; finish
  -- Phase 4: (R2, R1, R1) chain fires m times
  have p4 : ⟨2 * m + F + 2, 0, 2 * m, 2, 1⟩ [fm]⊢*
      ⟨F + m + 2, 0, 0, m + 2, 2 * m + 1⟩ := by
    have := r2r1r1_chain m (F + m + 2) 0 1 1
    rw [show 1 + 1 + m = m + 2 from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring,
        show F + m + 2 + m = 2 * m + F + 2 from by ring,
        show 0 + 2 * m = 2 * m from by ring] at this
    exact this
  -- Phase 5: R2 fires m+2 times
  have p5 : ⟨F + m + 2, 0, 0, m + 2, 2 * m + 1⟩ [fm]⊢*
      ⟨F, 2 * m + 4, 0, 0, 2 * m + 1⟩ := by
    rw [show F + m + 2 = F + (m + 2) from by ring]
    have := r2_chain (m + 2) F 0 (2 * m + 1)
    rw [show 0 + 2 * (m + 2) = 2 * m + 4 from by ring] at this
    exact this
  -- Phase 6: R3 fires 2*m+4 times
  have p6 : ⟨F, 2 * m + 4, 0, 0, 2 * m + 1⟩ [fm]⊢*
      ⟨4 * m + F + 8, 0, 0, 0, 4 * m + 5⟩ := by
    have := r3_chain (2 * m + 4) F (2 * m + 1)
    rw [show F + 2 * (2 * m + 4) = 4 * m + F + 8 from by ring,
        show 2 * m + 1 + (2 * m + 4) = 4 * m + 5 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus p2
      (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 p6))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 3⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, m⟩ ↦ ⟨2 * m + F + 3, 0, 0, 0, 2 * m + 1⟩) ⟨0, 1⟩
  intro ⟨F, m⟩
  refine ⟨⟨F + 1, 2 * m + 2⟩, ?_⟩
  show ⟨2 * m + F + 3, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺
    ⟨2 * (2 * m + 2) + (F + 1) + 3, 0, 0, 0, 2 * (2 * m + 2) + 1⟩
  rw [show 2 * (2 * m + 2) + (F + 1) + 3 = 4 * m + F + 8 from by ring,
      show 2 * (2 * m + 2) + 1 = 4 * m + 5 from by ring]
  exact main_trans F m

end Sz22_2003_unofficial_1688
