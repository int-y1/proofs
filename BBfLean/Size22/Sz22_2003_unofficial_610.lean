import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #610: [35/6, 121/2, 4/55, 9/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  2  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_610

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: (0, b, 0, d+k, e) ->* (0, b+2k, 0, d, e)
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R1,R1,R3 chain: (2, b+2k, c, d, e+k) ->* (2, b, c+k, d+2k, e)
theorem r1r1r3_chain : ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
  have many_step : ∀ k c d e, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- R3,R2,R2 chain: (0, 0, k, d, e+1) ->* (0, 0, 0, d, e+3*k+1)
theorem r3r2r2_chain : ⟨0, 0, k, d, e+1⟩ [fm]⊢* ⟨0, 0, 0, d, e+3*k+1⟩ := by
  have many_step : ∀ k e, ⟨0, 0, k, d, e+1⟩ [fm]⊢* ⟨0, 0, 0, d, e+3*k+1⟩ := by
    intro k; induction' k with k h <;> intro e
    · exists 0
    step fm; step fm; step fm
    rw [show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k e

-- Main transition: (0,0,0,d,e) ->+ (0,0,0,2d+1,e+2d+1) for d >= 1, e >= d+2
-- Parametrize: d = D+1, e = E+D+3 where D >= 0, E >= 0
theorem main_trans (hd : d ≥ 1) (he : e ≥ d + 2) :
    ⟨0, 0, 0, d, e⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 2*d+1, e+2*d+1⟩ := by
  obtain ⟨D, rfl⟩ : ∃ D, d = D + 1 := ⟨d - 1, by omega⟩
  obtain ⟨E, rfl⟩ : ∃ E, e = E + D + 3 := ⟨e - D - 3, by omega⟩
  -- Phase A: drain d via R4: (0,0,0,D+1,E+D+3) -> (0,2D+2,0,0,E+D+3)
  rw [show (D + 1 : ℕ) = 0 + (D + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0) (k := D + 1) (e := E + D + 3))
  simp only [Nat.zero_add]
  -- State: (0, 2*(D+1), 0, 0, E+D+3)
  -- Phase B1: R5+R1+R3 (3 steps): (0, 2D+2, 0, 0, E+D+3) -> (2, 2D+1, 0, 2, E+D+1)
  rw [show 2 * (D + 1) = (2 * D) + 2 from by ring,
      show E + D + 3 = (E + D + 1) + 2 from by ring]
  step fm; step fm; step fm
  -- State: (2, 2*D+1, 0, 2, E+D+1)
  -- Phase B2: R1,R1,R3 chain with b=1, k=D: (2, 1+2D, 0, 2, E+1+D) -> (2, 1, D, 2+2D, E+1)
  rw [show 2 * D + 1 = 1 + 2 * D from by ring,
      show E + D + 1 = (E + 1) + D from by ring]
  apply stepStar_trans (r1r1r3_chain (b := 1) (k := D) (c := 0) (d := 2) (e := E + 1))
  simp only [Nat.zero_add]
  -- State: (2, 1, D, 2+2*D, E+1)
  -- Phase B3+C: R1 then R2: (2, 1, D, 2+2D, E+1) -> (1, 0, D+1, 3+2D, E+1) -> (0, 0, D+1, 3+2D, E+3)
  step fm; step fm
  -- State: (0, 0, D+1, 2+2*D+1, E+2+1)
  -- Phase D: R3,R2,R2 chain
  rw [show 2 + 2 * D + 1 = 3 + 2 * D from by ring,
      show E + 2 + 1 = (E + 2) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (k := D + 1) (d := 3 + 2 * D) (e := E + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 1 ∧ e ≥ d + 2)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    exact ⟨⟨0, 0, 0, 2*d+1, e+2*d+1⟩,
      ⟨2*d+1, e+2*d+1, rfl, by omega, by omega⟩,
      main_trans hd he⟩
  · exact ⟨1, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_610
