import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1721: [8/15, 147/22, 35/2, 11/7, 3/11]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0  2 -1
-1  0  1  1  0
 0  0  0 -1  1
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1721

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 chain: drain a, fill c and d
theorem r3_chain : ∀ k, ∀ C D,
    ⟨k, 0, C, D, 0⟩ [fm]⊢* ⟨0, 0, C + k, D + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro C D
  · exists 0
  · step fm
    apply stepStar_trans (ih (C + 1) (D + 1))
    rw [show C + 1 + k = C + (k + 1) from by ring,
        show D + 1 + k = D + (k + 1) from by ring]; finish

-- R4 chain: drain d, fill e
theorem r4_chain : ∀ k, ∀ C E,
    ⟨0, 0, C, k, E⟩ [fm]⊢* ⟨0, 0, C, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro C E
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih C (E + 1))
    rw [show E + 1 + k = E + (k + 1) from by ring]; finish

-- (R2, R1) chain: (A+1, 0, k, D, E+k) ->* (A+1+2k, 0, 0, D+2k, E)
theorem r2r1_chain : ∀ k, ∀ A D E,
    ⟨A + 1, 0, k, D, E + k⟩ [fm]⊢* ⟨A + 1 + 2 * k, 0, 0, D + 2 * k, E⟩ := by
  intro k; induction' k with k ih <;> intro A D E
  · simp; exists 0
  · rw [show E + (k + 1) = (E + k) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (A + 2) (D + 2) E)
    rw [show A + 2 + 1 + 2 * k = A + 1 + 2 * (k + 1) from by ring,
        show D + 2 + 2 * k = D + 2 * (k + 1) from by ring]; finish

-- R2 chain with b: (A+k, B, 0, D, k) ->* (A, B+k, 0, D+2k, 0) when c=0
theorem r2_chain_b : ∀ k, ∀ A B D,
    ⟨A + k, B, 0, D, k⟩ [fm]⊢* ⟨A, B + k, 0, D + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B D
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih A (B + 1) (D + 2))
    rw [show B + 1 + k = B + (k + 1) from by ring,
        show D + 2 + 2 * k = D + 2 * (k + 1) from by ring]; finish

-- (R3, R1) chain: drain b, fill a and d.
-- (A+1, k, 0, D, 0) ->* (A+1+2k, 0, 0, D+k, 0)
-- Need A+1 to ensure R3 fires (a >= 1)
theorem r3r1_chain : ∀ k, ∀ A D,
    ⟨A + 1, k, 0, D, 0⟩ [fm]⊢* ⟨A + 1 + 2 * k, 0, 0, D + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (A + 2) (D + 1))
    rw [show A + 2 + 1 + 2 * k = A + 1 + 2 * (k + 1) from by ring,
        show D + 1 + k = D + (k + 1) from by ring]; finish

-- Main transition: (a+1, 0, 0, d, 0) ⊢⁺ (2a+d+3, 0, 0, 2a+3d, 0)
-- Requires d ≤ 2a for the R2 drain and R3R1 phases
theorem main_trans (a d : ℕ) (h : d ≤ 2 * a) :
    ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨2 * a + d + 3, 0, 0, 2 * a + 3 * d, 0⟩ := by
  -- Phase 1: R3 x (a+1): (a+1, 0, 0, d, 0) -> (0, 0, a+1, d+a+1, 0)
  have p1 : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢* ⟨0, 0, a + 1, d + (a + 1), 0⟩ := by
    have := r3_chain (a + 1) 0 d
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: R4 x (d+a+1): -> (0, 0, a+1, 0, d+a+1)
  have p2 : ⟨0, 0, a + 1, d + (a + 1), 0⟩ [fm]⊢* ⟨0, 0, a + 1, 0, d + a + 1⟩ := by
    have := r4_chain (d + (a + 1)) (a + 1) 0
    rw [show 0 + (d + (a + 1)) = d + a + 1 from by ring] at this; exact this
  -- Phase 3a: R5, R1: (0, 0, a+1, 0, d+a+1) -> (3, 0, a, 0, d+a)
  have p3a : ⟨0, 0, a + 1, 0, d + a + 1⟩ [fm]⊢⁺ ⟨3, 0, a, 0, d + a⟩ := by
    rw [show d + a + 1 = (d + a) + 1 from by ring,
        show a + 1 = a + 1 from rfl]
    step fm; step fm; ring_nf; finish
  -- Phase 3b: (R2, R1) x a: (3, 0, a, 0, d+a) -> (2a+3, 0, 0, 2a, d)
  have p3b : ⟨3, 0, a, 0, d + a⟩ [fm]⊢* ⟨2 * a + 3, 0, 0, 2 * a, d⟩ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl]
    have := r2r1_chain a 2 0 d
    rw [show 2 + 1 + 2 * a = 2 * a + 3 from by ring,
        show 0 + 2 * a = 2 * a from by ring] at this
    exact this
  -- Phase 4: R2 x d: (2a+3, 0, 0, 2a, d) -> (2a+3-d, d, 0, 2a+2d, 0)
  have p4 : ⟨2 * a + 3, 0, 0, 2 * a, d⟩ [fm]⊢*
      ⟨2 * a + 3 - d, d, 0, 2 * a + 2 * d, 0⟩ := by
    have h4 : 2 * a + 3 - d + d = 2 * a + 3 := by omega
    have := r2_chain_b d (2 * a + 3 - d) 0 (2 * a)
    rw [show 0 + d = d from by ring, h4] at this; exact this
  -- Phase 5: (R3, R1) x d: -> (2a+d+3, 0, 0, 2a+3d, 0)
  have p5 : ⟨2 * a + 3 - d, d, 0, 2 * a + 2 * d, 0⟩ [fm]⊢*
      ⟨2 * a + d + 3, 0, 0, 2 * a + 3 * d, 0⟩ := by
    rw [show 2 * a + 3 - d = (2 * a + 2 - d) + 1 from by omega]
    have := r3r1_chain d (2 * a + 2 - d) (2 * a + 2 * d)
    rw [show 2 * a + 2 - d + 1 + 2 * d = 2 * a + d + 3 from by omega,
        show 2 * a + 2 * d + d = 2 * a + 3 * d from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus (stepStar_trans p1 p2)
    (stepPlus_stepStar_stepPlus p3a
      (stepStar_trans p3b (stepStar_trans p4 p5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = (⟨a + 1, 0, 0, d, 0⟩ : Q) ∧ d ≤ 2 * a)
  · intro q ⟨a, d, hq, hle⟩; subst hq
    exact ⟨⟨2 * a + d + 3, 0, 0, 2 * a + 3 * d, 0⟩,
           ⟨2 * a + d + 2, 2 * a + 3 * d, by ring_nf, by omega⟩,
           main_trans a d hle⟩
  · exact ⟨0, 0, by simp [c₀], by omega⟩

end Sz22_2003_unofficial_1721
