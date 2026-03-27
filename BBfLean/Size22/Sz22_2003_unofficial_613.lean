import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #613: [35/6, 121/2, 4/55, 9/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  2  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_613

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b (b d k e : ℕ) : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  induction k generalizing b with
  | zero => exists 0
  | succ k ih =>
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih (b + 2)); ring_nf; finish

-- R3,R1,R1 chain: (0, 2(k+1), c+1, d, e+k+1) →* (0, 0, c+k+2, d+2k+2, e)
theorem r3r1r1_chain (k c d e : ℕ) : ⟨0, 2*(k+1), c+1, d, e+k+1⟩ [fm]⊢*
    ⟨0, 0, c+k+2, d+2*k+2, e⟩ := by
  induction k generalizing c d e with
  | zero =>
    step fm; step fm; step fm; ring_nf; finish
  | succ k ih =>
    rw [show 2 * (k + 1 + 1) = (2 * (k + 1)) + 1 + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

-- R3,R2,R2 chain: (0, 0, c+k, d, e+1) →* (0, 0, c, d, e+3*k+1)
theorem r3r2r2_chain (k c d e : ℕ) : ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+3*k+1⟩ := by
  induction k generalizing c e with
  | zero => exists 0
  | succ k ih =>
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih c (e + 3))
    ring_nf; finish

-- Main transition: (0, 0, 0, D+1, E+D+3) →⁺ (0, 0, 0, 2*D+3, E+3*D+7)
theorem main_trans (D E : ℕ) : ⟨0, 0, 0, D+1, E+D+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*D+3, E+3*D+7⟩ := by
  -- Phase 1: d_to_b: →* (0, 2D+2, 0, 0, E+D+3)
  rw [show D + 1 = 0 + (D + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b 0 0 (D+1) (E+D+3))
  rw [show 0 + 2 * (D + 1) = 2 * D + 2 from by ring]
  -- Phase 2: R5 (gives ⊢⁺), R1
  rw [show E + D + 3 = (E + D + 2) + 1 from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Now at (1, 2D+3, 0, 0, E+D+2)
  rw [show 2 * D + 2 + 1 = (2 * D + 2) + 1 from by ring]
  step fm
  -- Now at (0, 2D+2, 1, 1, E+D+2) = (0, 2*(D+1), 0+1, 1, (E+1)+D+1)
  -- Phase 3: r3r1r1_chain(k=D, c=0, d=1, e=E+1)
  rw [show E + D + 2 = (E + 1) + D + 1 from by ring,
      show 2 * D + 2 = 2 * (D + 1) from by ring]
  apply stepStar_trans (r3r1r1_chain D 0 1 (E+1))
  -- Now at (0, 0, D+2, 2D+3, E+1) = (0, 0, 0+(D+2), 2D+3, E+0+1)
  -- Phase 4: r3r2r2_chain(k=D+2, c=0, d=2D+3, e=E)
  rw [show (0 : ℕ) + D + 2 = 0 + (D + 2) from by ring,
      show (1 : ℕ) + 2 * D + 2 = 2 * D + 3 from by ring,
      show E + 1 = E + 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (D+2) 0 (2*D+3) (E+0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d+1, e+d+3⟩) ⟨0, 1⟩
  intro ⟨d, e⟩
  refine ⟨⟨2*d+2, e+d+2⟩, ?_⟩
  show ⟨0, 0, 0, d+1, e+d+3⟩ [fm]⊢⁺ ⟨0, 0, 0, (2*d+2)+1, (e+d+2)+(2*d+2)+3⟩
  rw [show (2*d+2)+1 = 2*d+3 from by ring,
      show (e+d+2)+(2*d+2)+3 = e+3*d+7 from by ring]
  exact main_trans d e

end Sz22_2003_unofficial_613
