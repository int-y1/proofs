import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #618: [35/6, 121/2, 8/55, 3/7, 35/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 3  0 -1  0 -1
 0  1  0 -1  0
 0  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_618

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b (a=0, c=0, accumulating b)
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, (e : ℕ)⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

-- R3+R2x3 drain c to 0 (a=0, b=0)
theorem drain : ∀ k e, ⟨0, 0, k, (d : ℕ), e+1⟩ [fm]⊢* ⟨0, 0, 0, d, e+5*k+1⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

-- Interleaved R1/R3 phase then R2 and c drain
-- (3, B, C, D, E+B+1) ⊢* (0, 0, 0, D+B, E+4*B+5*C+7)
theorem interleaved : ∀ B, ∀ C D E,
    ⟨3, B, C, D, (E : ℕ)+B+1⟩ [fm]⊢* ⟨0, 0, 0, D+B, E+4*B+5*C+7⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro C D E
  rcases B with _ | _ | _ | B'
  · -- B=0: R2x3 → (0,0,C,D,E+7), then drain C
    rw [show E + 0 + 1 = E + 1 from by ring]
    step fm; step fm; step fm
    rw [show E + 1 + 2 + 2 + 2 = (E + 6) + 1 from by ring]
    apply stepStar_trans (drain C (E + 6))
    ring_nf; finish
  · -- B=1: R1, R2x2, drain (C+1)
    rw [show E + 1 + 1 = E + 1 + 1 from rfl]
    step fm; step fm; step fm
    rw [show E + 1 + 1 + 2 + 2 = (E + 5) + 1 from by ring]
    apply stepStar_trans (drain (C + 1) (E + 5))
    ring_nf; finish
  · -- B=2: R1x2, R2, drain (C+2)
    rw [show E + (1 + 1) + 1 = E + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show E + 1 + 1 + 1 + 2 = (E + 4) + 1 from by ring,
        show C + 1 + 1 = C + 2 from by ring,
        show D + 1 + 1 = D + 2 from by ring]
    apply stepStar_trans (drain (C + 2) (E + 4))
    ring_nf; finish
  · -- B=B'+3: R1x3 then R3, then IH for B'
    rw [show E + (B' + 3) + 1 = E + B' + 1 + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show D + 1 + 1 + 1 = D + 3 from by ring,
        show E + B' + 1 + 1 + 1 = (E + 2) + B' + 1 from by ring]
    apply stepStar_trans (ih B' (by omega) (C + 2) (D + 3) (E + 2))
    ring_nf; finish

-- Main transition: one full cycle
theorem main_trans :
    ⟨0, 0, 0, d+1, e+3*d+5⟩ [fm]⊢⁺ ⟨0, 0, 0, d+2, e+6*d+12⟩ := by
  -- Phase 1: R4 x (d+1) → (0, d+1, 0, 0, e+3*d+5)
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d+1) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5 + R3 → (3, d+1, 0, 1, e+3*d+3)
  rw [show e + 3 * d + 5 = (e + 3 * d + 3) + 1 + 1 from by ring]
  step fm; step fm
  -- Phase 3: interleaved with B=d+1, C=0, D=1, E=e+2*d+1
  rw [show e + 3 * d + 3 = (e + 2 * d + 1) + (d + 1) + 1 from by ring]
  apply stepStar_trans (interleaved (d+1) 0 1 (e+2*d+1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 6⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d+1, e+3*d+5⟩) ⟨0, 1⟩
  intro ⟨d, e⟩; exists ⟨d+1, e+3*d+4⟩
  show ⟨0, 0, 0, d+1, e+3*d+5⟩ [fm]⊢⁺ ⟨0, 0, 0, d+2, (e+3*d+4)+3*(d+1)+5⟩
  rw [show (e + 3 * d + 4) + 3 * (d + 1) + 5 = e + 6 * d + 12 from by ring]
  apply main_trans

end Sz22_2003_unofficial_618
