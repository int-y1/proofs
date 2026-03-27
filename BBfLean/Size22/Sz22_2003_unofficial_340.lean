import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #340: [189/10, 5/33, 14/3, 11/7, 15/2]

Vector representation:
```
-1  3 -1  1  0
 0 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_340

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+3, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: transfer d to e
theorem d_to_e : ∀ k a e, ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]; finish

-- R1/R2 alternating loop: each pair consumes 1 from a and 1 from e
theorem r1r2_loop : ∀ k b d e,
    ⟨k, b, 1, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 1, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 2) (d + 1) e)
    rw [show b + 2 + 2 * k = b + 2 * (k + 1) from by ring,
        show d + 1 + k = d + (k + 1) from by ring]; finish

-- R2 chain: consume e, build c
theorem r2_chain : ∀ k b c d, ⟨0, b + k, c, d, k⟩ [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · simp; exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d)
    rw [show c + 1 + k = c + (k + 1) from by ring]; finish

-- R3/R1 loop: consume c, grow b and d
theorem r3r1_loop : ∀ k b d,
    ⟨0, b + 1, k + 1, d, 0⟩ [fm]⊢* ⟨0, b + 2 * k + 3, 0, d + 2 * k + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · step fm; step fm; finish
  · step fm; step fm
    rw [show b + 3 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih (b + 2) (d + 2))
    rw [show b + 2 + 2 * k + 3 = b + 2 * (k + 1) + 3 from by ring,
        show d + 2 + 2 * k + 2 = d + 2 * (k + 1) + 2 from by ring]; finish

-- R3 chain: transfer b to a and d
theorem b_to_a : ∀ k a d, ⟨a, k + 1, 0, d, 0⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; finish
  · step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
        show d + 1 + k + 1 = d + (k + 1) + 1 from by ring]; finish

-- Main cycle: one full iteration of the canonical state
-- From (a+1, 0, 0, a+m+1, 0) with m+1 ≤ 2*a, reach (2a+m+4, 0, 0, 3a+3m+8, 0)
theorem main_cycle (a m : ℕ) (h : m + 1 ≤ 2 * a) :
    ⟨a + 1, 0, 0, a + m + 1, 0⟩ [fm]⊢⁺ ⟨2 * a + m + 4, 0, 0, 3 * a + 3 * m + 8, 0⟩ := by
  -- Phase 1: R4 chain: (a+1, 0, 0, a+m+1, 0) ->* (a+1, 0, 0, 0, a+m+1)
  apply stepStar_stepPlus_stepPlus
  · have h1 := d_to_e (a + m + 1) (a + 1) 0
    rw [show 0 + (a + m + 1) = a + m + 1 from by ring] at h1; exact h1
  -- Phase 2: R5 step: (a+1, 0, 0, 0, a+m+1) -> (a, 1, 1, 0, a+m+1)
  step fm
  -- Phase 3: R1/R2 loop (a iterations): (a, 1, 1, 0, a+m+1) ->* (0, 2a+1, 1, a, m+1)
  apply stepStar_trans
  · have h3 := r1r2_loop a 1 0 (m + 1)
    rw [show m + 1 + a = a + m + 1 from by ring,
        show 1 + 2 * a = 2 * a + 1 from by ring,
        show 0 + a = a from by ring] at h3; exact h3
  -- Phase 4: R2 chain (m+1 iterations): (0, 2a+1, 1, a, m+1) ->* (0, 2a-m, m+2, a, 0)
  -- We need 2a+1 = (2a-m) + (m+1), i.e., b_base = 2a - m.
  -- Since m+1 ≤ 2a, we have m ≤ 2a-1, so 2a-m ≥ 1.
  apply stepStar_trans
  · have h4 := r2_chain (m + 1) (2 * a - m) 1 a
    rw [show 2 * a - m + (m + 1) = 2 * a + 1 from by omega,
        show 1 + (m + 1) = m + 2 from by ring] at h4; exact h4
  -- Phase 5: R3/R1 loop (m+2 iterations): (0, 2a-m, m+2, a, 0) ->* (0, 2a+m+6, 0, 3a+2m+6, 0)
  -- Write 2a-m = (2a-m-1)+1 (since 2a-m ≥ 1) and m+2 = (m+1)+1
  apply stepStar_trans
  · have h5 := r3r1_loop (m + 1) (2 * a - m - 1) a
    rw [show 2 * a - m - 1 + 1 = 2 * a - m from by omega,
        show 2 * a - m - 1 + 2 * (m + 1) + 3 = 2 * a + m + 4 from by omega,
        show a + 2 * (m + 1) + 2 = a + 2 * m + 4 from by ring] at h5; exact h5
  -- Phase 6: R3 chain: (0, 2a+m+4, 0, a+2m+4, 0) ->* (2a+m+4, 0, 0, 3a+3m+8, 0)
  have h6 := b_to_a (2 * a + m + 3) 0 (a + 2 * m + 4)
  rw [show 0 + (2 * a + m + 3) + 1 = 2 * a + m + 4 from by ring,
      show a + 2 * m + 4 + (2 * a + m + 3) + 1 = 3 * a + 3 * m + 8 from by ring] at h6; exact h6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 5, 0⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a m, q = (⟨a + 1, 0, 0, a + m + 1, 0⟩ : Q) ∧ m + 1 ≤ 2 * a)
  · intro q ⟨a, m, hq, hm⟩; subst hq
    refine ⟨⟨2 * a + m + 4, 0, 0, 3 * a + 3 * m + 8, 0⟩,
           ⟨2 * a + m + 3, a + 2 * m + 4, ?_, ?_⟩,
           main_cycle a m hm⟩
    · ring_nf
    · omega
  · exact ⟨2, 2, by ring_nf, by omega⟩

end Sz22_2003_unofficial_340
