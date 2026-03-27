import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #593: [35/6, 121/2, 28/55, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  1 -1
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_593

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- R3,R2,R2 chain: drain c register
theorem r3r2r2_chain : ⟨0, 0, k+1, d, e+1⟩ [fm]⊢* ⟨0, 0, 0, d+k+1, e+3*k+4⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, k+1, d, e+1⟩ [fm]⊢* ⟨0, 0, 0, d+k+1, e+3*k+4⟩ := by
    intro k; induction' k with k h <;> intro d e
    · step fm; step fm; step fm; ring_nf; finish
    rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h (d+1) (e+3))
    ring_nf; finish
  exact many_step k d e

-- R3,R1,R1 chain: each round b-=2, c+=1, d+=3, e-=1
theorem r3r1r1_chain : ⟨0, b+2*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+k+1, d+3*k, e⟩ := by
  have many_step : ∀ k c d e, ⟨0, b+2*k, c+1, d, e+k⟩ [fm]⊢* ⟨0, b, c+k+1, d+3*k, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h (c+1) (d+3) e)
    ring_nf; finish
  exact many_step k c d e

-- R3,R1,R2 tail: handle b=1 remainder
theorem r3r1r2_tail : ⟨0, 1, c+1, d, e+1⟩ [fm]⊢* ⟨0, 0, c+1, d+2, e+2⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Phase: d_to_b + R5 combined
theorem d_to_b_r5 : ⟨0, 0, 0, D+1, E+1⟩ [fm]⊢* ⟨0, D+1, 1, 0, E⟩ := by
  rw [show D + 1 = 0 + (D + 1) from by ring]
  apply stepStar_trans (d_to_b (b := 0) (d := 0) (k := D+1) (e := E+1))
  simp only [Nat.zero_add]
  step fm; finish

-- Even D = 2K: full interleave from (0, 2K+1, 1, 0, E+2K+3)
-- Phases: r3r1r1 (K rounds, b=1), r3r1r2 tail, r3r2r2 (K+1 rounds)
-- Result: (0, 0, 0, 4K+3, 4K+E+7)
theorem even_d_interleave :
    ⟨0, 2*K+1, 1, 0, E+2*K+3⟩ [fm]⊢* ⟨0, 0, 0, 4*K+3, 4*K+E+7⟩ := by
  -- r3r1r1_chain with b=1, k=K
  rw [show 2 * K + 1 = 1 + 2 * K from by ring,
      show E + 2 * K + 3 = (E + K + 3) + K from by ring]
  apply stepStar_trans (r3r1r1_chain (b := 1) (c := 0) (d := 0) (k := K) (e := E+K+3))
  simp only [Nat.zero_add]
  -- r3r1r2_tail
  rw [show E + K + 3 = (E + K + 2) + 1 from by ring]
  apply stepStar_trans (r3r1r2_tail (c := K) (d := 3*K) (e := E+K+2))
  -- r3r2r2_chain
  rw [show E + K + 2 + 2 = (E + K + 3) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (k := K) (d := 3*K+2) (e := E+K+3))
  ring_nf; finish

-- Odd D = 2K+1: full interleave from (0, 2(K+1), 1, 0, E+2K+4)
-- Phases: r3r1r1 (K+1 rounds, b=0), r3r2r2 (K+2 rounds)
-- Result: (0, 0, 0, 4K+5, 4K+E+9)
theorem odd_d_interleave :
    ⟨0, 2*(K+1), 1, 0, E+2*K+4⟩ [fm]⊢* ⟨0, 0, 0, 4*K+5, 4*K+E+9⟩ := by
  -- r3r1r1_chain with b=0, k=K+1
  rw [show 2 * (K + 1) = 0 + 2 * (K + 1) from by ring,
      show E + 2 * K + 4 = (E + K + 3) + (K + 1) from by ring]
  apply stepStar_trans (r3r1r1_chain (b := 0) (c := 0) (d := 0) (k := K+1) (e := E+K+3))
  simp only [Nat.zero_add]
  -- r3r2r2_chain
  rw [show K + 1 + 0 + 1 = (K + 1) + 1 from by ring,
      show E + K + 3 = (E + K + 2) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (k := K+1) (d := 3*(K+1)) (e := E+K+2))
  ring_nf; finish

-- Full transition: (0, 0, 0, D+1, E+D+4) ⊢⁺ (0, 0, 0, 2D+3, 2D+E+7)
theorem full_trans : ⟨0, 0, 0, D+1, E+D+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*D+3, 2*D+E+7⟩ := by
  rw [show E + D + 4 = (E + D + 3) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b_r5 (D := D) (E := E+D+3))
  -- Now need: (0, D+1, 1, 0, E+D+3) ⊢⁺ (0, 0, 0, 2D+3, 2D+E+7)
  -- The interleave lemmas give ⊢*. Convert via stepStar_stepPlus with ≠.
  rcases Nat.even_or_odd D with ⟨K, hK⟩ | ⟨K, hK⟩
  · subst hK
    rw [show K + K + 1 = 2 * K + 1 from by ring,
        show E + (K + K) + 3 = E + 2 * K + 3 from by ring,
        show 2 * (K + K) + 3 = 4 * K + 3 from by ring,
        show 2 * (K + K) + E + 7 = 4 * K + E + 7 from by ring]
    apply stepStar_stepPlus (even_d_interleave (K := K) (E := E))
    simp [Q]
  · subst hK
    rw [show 2 * K + 1 + 1 = 2 * (K + 1) from by ring,
        show E + (2 * K + 1) + 3 = E + 2 * K + 4 from by ring,
        show 2 * (2 * K + 1) + 3 = 4 * K + 5 from by ring,
        show 2 * (2 * K + 1) + E + 7 = 4 * K + E + 9 from by ring]
    apply stepStar_stepPlus (odd_d_interleave (K := K) (E := E))
    simp [Q]

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D+1, E+D+4⟩)
  · intro c ⟨D, E, hq⟩; subst hq
    refine ⟨⟨0, 0, 0, 2*D+3, 2*D+E+7⟩, ⟨2*D+2, E+1, ?_⟩, full_trans⟩
    show (0, 0, 0, 2*D+3, 2*D+E+7) = (0, 0, 0, 2*D+2+1, E+1+(2*D+2)+4)
    ring_nf
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_593
