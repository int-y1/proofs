import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1781: [9/10, 3773/2, 2/21, 5/11, 33/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  3  1
 1 -1  0 -1  0
 0  0  1  0 -1
 0  1  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1781

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Phase 1: R4 repeated. (0, 0, C, d, k) →* (0, 0, C+k, d, 0)
theorem e_to_c : ∀ k : ℕ, ∀ C d, ⟨(0 : ℕ), 0, C, d, k⟩ [fm]⊢* ⟨0, 0, C + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro C d
  · rw [show C + 0 = C from by ring]; exists 0
  · step fm
    apply stepStar_trans (ih (C + 1) d)
    rw [show C + 1 + k = C + (k + 1) from by ring]; finish

-- Phase 2: R3/R1 chain. (0, B+1, k+1, D+k+1, 1) →* (0, B+k+2, 0, D, 1)
theorem r3r1_chain : ∀ k : ℕ, ∀ B D, ⟨(0 : ℕ), B + 1, k + 1, D + k + 1, 1⟩ [fm]⊢* ⟨0, B + k + 2, 0, D, 1⟩ := by
  intro k; induction' k with k ih <;> intro B D
  · step fm; step fm; rw [show B + 0 + 2 = B + 2 from by ring]; finish
  · step fm
    step fm
    rw [show B + 2 = (B + 1) + 1 from by ring]
    apply stepStar_trans (ih (B + 1) D)
    rw [show B + 1 + k + 2 = B + (k + 1) + 2 from by ring]; finish

-- Phase 3: R3/R2 drain. (0, k+1, 0, D+1, E) →* (0, 0, 0, D+2*k+3, E+k+1)
theorem r3r2_drain : ∀ k : ℕ, ∀ D E, ⟨(0 : ℕ), k + 1, 0, D + 1, E⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * k + 3, E + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · step fm; step fm; rw [show D + 2 * 0 + 3 = D + 3 from by ring, show E + 0 + 1 = E + 1 from by ring]; finish
  · step fm
    step fm
    rw [show D + 3 = (D + 2) + 1 from by ring]
    apply stepStar_trans (ih (D + 2) (E + 1))
    rw [show D + 2 + 2 * k + 3 = D + 2 * (k + 1) + 3 from by ring,
        show E + 1 + k + 1 = E + (k + 1) + 1 from by ring]; finish

-- Combined: R5 + R3/R1. (0, 0, e+1, d+e+2, 0) →⁺ (0, e+2, 0, d, 1)
theorem r5_r3r1 (d e : ℕ) : ⟨(0 : ℕ), 0, e + 1, d + e + 2, 0⟩ [fm]⊢⁺ ⟨0, e + 2, 0, d, 1⟩ := by
  step fm -- R5: (0, 1, e+1, d+e+1, 1)
  rw [show d + e + 1 = d + e + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1_chain e 0 d)
  rw [show 0 + e + 2 = e + 2 from by ring]; finish

-- Main transition: (0, 0, 0, d+e+3, e+1) →⁺ (0, 0, 0, d+2*e+5, e+3)
theorem main_trans (d e : ℕ) : ⟨(0 : ℕ), 0, 0, d + e + 3, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2 * e + 5, e + 3⟩ := by
  -- Phase 1: move e+1 to c: (0,0,0,d+e+3,e+1) →* (0,0,e+1,d+e+3,0)
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans (e_to_c (e + 1) 0 (d + e + 3))
    rw [show 0 + (e + 1) = e + 1 from by ring]; finish
  -- Phase 2: R5 + R3/R1: (0,0,e+1,d+e+3,0) →⁺ (0,e+2,0,d+1,1)
  rw [show d + e + 3 = (d + 1) + e + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r5_r3r1 (d + 1) e)
  -- Phase 3: R3/R2 drain: (0,e+2,0,d+1,1) →* (0,0,0,d+2*e+5,e+3)
  rw [show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (r3r2_drain (e + 1) d 1)
  rw [show d + 2 * (e + 1) + 3 = d + 2 * e + 5 from by ring,
      show 1 + (e + 1) + 1 = e + 3 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + e + 3, e + 1⟩) ⟨0, 0⟩
  intro ⟨d, e⟩; exists ⟨d + e, e + 2⟩
  show ⟨(0 : ℕ), 0, 0, d + e + 3, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, (d + e) + (e + 2) + 3, (e + 2) + 1⟩
  rw [show (d + e) + (e + 2) + 3 = d + 2 * e + 5 from by ring,
      show (e + 2) + 1 = e + 3 from by ring]
  exact main_trans d e

end Sz22_2003_unofficial_1781
