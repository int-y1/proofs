import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #611: [35/6, 121/2, 4/55, 9/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  2  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_611

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: each step converts one d to b+2
theorem d_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3R2R2 chain: each round converts one c, gaining net e+3
theorem r3r2r2_chain : ∀ k, ∀ d e, ⟨0, 0, k, d, e+1⟩ [fm]⊢* ⟨0, 0, 0, d, e+3*k+1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R1R1R3 chain: three-step rounds (R1, R1, R3)
theorem r1r1r3_chain : ∀ n, ∀ j D E,
    ⟨2, 2*n+3, j, D, E+n+1⟩ [fm]⊢* ⟨2, 1, j+n+1, D+2*n+2, E⟩ := by
  intro n; induction' n with n ih <;> intro j D E
  · step fm; step fm; step fm; finish
  rw [show 2 * (n + 1) + 3 = (2 * n + 3) + 1 + 1 from by ring,
      show E + (n + 1) + 1 = (E + 1) + n + 1 from by ring]
  step fm; step fm
  -- State has e = E+1+n+1 = (E+1+n)+1 (by Lean def of Nat.add on succ)
  -- R3 fires: c is (j+1)+1, e is (E+1+n)+1
  step fm
  -- After R3: (2, 2*n+3, j+1, D+1+1, E+1+n)
  rw [show E + 1 + n = E + n + 1 from by ring]
  apply stepStar_trans (ih (j+1) (D+1+1) E)
  ring_nf; finish

-- Main transition: (0,0,0,d+1,e+d+3) ->+ (0,0,0,2*d+3,e+3*d+8)
theorem main_transition :
    ⟨0, 0, 0, d+1, e+d+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*d+3, e+3*d+8⟩ := by
  -- Phase 1: R4 (d+1 times): (0,0,0,d+1,e+d+3) ->* (0,2*d+2,0,0,e+d+3)
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d+1) 0 0 (e+d+3))
  simp only [Nat.zero_add]
  -- Phase 2: R5 then R3: (0,2*d+2,0,0,e+d+3) -> (2,2*d+3,0,0,e+d+1)
  rw [show 2 * (d + 1) = 2 * d + 2 from by ring,
      show e + d + 3 = (e + d + 1) + 1 + 1 from by ring]
  step fm; step fm
  -- Phase 3: R1R1R3 chain (d+1 rounds):
  -- State: (2, 2*d+2+1, 0, 0, e+d+1)
  -- Need: (2, 2*d+3, 0, 0, e+d+1) = (2, 2*d+3, 0, 0, E+d+1) with E=e
  -- r1r1r3_chain d: (2, 2*d+3, 0, 0, e+d+1) ->* (2, 1, 0+d+1, 0+2*d+2, e)
  rw [show 2 * d + 2 + 1 = 2 * d + 3 from by ring]
  apply stepStar_trans (r1r1r3_chain d 0 0 e)
  simp only [Nat.zero_add]
  -- Phase 4: R1 then R2: (2, 1, d+1, 2*d+2, e) -> (0, 0, d+2, 2*d+3, e+2)
  rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring]
  step fm; step fm
  -- Phase 5: R3R2R2 chain (d+2 rounds)
  rw [show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (d+2) (2*d+3) (e+1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 5⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d+1, e+d+3⟩) ⟨0, 2⟩
  intro ⟨d, e⟩
  refine ⟨⟨2*d+2, e+d+3⟩, ?_⟩
  show ⟨0, 0, 0, d+1, e+d+3⟩ [fm]⊢⁺ ⟨0, 0, 0, (2*d+2)+1, (e+d+3)+(2*d+2)+3⟩
  rw [show (2 * d + 2) + 1 = 2 * d + 3 from by ring,
      show (e + d + 3) + (2 * d + 2) + 3 = e + 3 * d + 8 from by ring]
  exact main_transition
