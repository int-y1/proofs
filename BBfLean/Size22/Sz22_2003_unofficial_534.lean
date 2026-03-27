import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #534: [28/15, 63/22, 25/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  2  0  1 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_534

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 repeated: convert a to c (a needs ≥1, b=0, e=0)
theorem a_to_c : ∀ k c, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _)
  rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]
  finish

-- R4 repeated: convert d to e (a=0, b=0)
theorem d_to_e : ∀ k d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  rw [show e + 1 + k = e + (k + 1) from by ring]
  finish

-- R5+R1: opening two steps from (0, 0, c+2, 0, e) to (2, 0, c, 1, e)
theorem open_r5r1 : ⟨0, 0, c+2, 0, e⟩ [fm]⊢⁺ ⟨2, 0, c, 1, e⟩ := by
  step fm; step fm; finish

-- R2+R1+R1 chain: (a+2, 0, c+2*k, d+1, k) →* (a+3*k+2, 0, c, d+3*k+1, 0)
theorem r2r1r1_chain : ∀ k a d, ⟨a+2, 0, c+2*k, d+1, k⟩ [fm]⊢* ⟨a+3*k+2, 0, c, d+3*k+1, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by ring,
      show a + 2 = (a + 1) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h (a + 3) (d + 3))
  ring_nf; finish

-- Main transition: (d+1, 0, 0, d, 0) →⁺ (3*d+2, 0, 0, 3*d+1, 0)
theorem main_trans : ⟨d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨3*d+2, 0, 0, 3*d+1, 0⟩ := by
  -- Phase 1: R3 chain (d+1 times): (d+1, 0, 0, d, 0) →* (0, 0, 2*(d+1), d, 0)
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_c (a := 0) (d := d) (d + 1) 0)
  rw [show 0 + 2 * (d + 1) = (2 * d) + 2 from by ring]
  -- Phase 2: R4 chain (d times): (0, 0, 2*d+2, d, 0) →* (0, 0, 2*d+2, 0, d)
  have h2 := d_to_e (c := 2 * d + 2) d 0 0
  simp only [Nat.zero_add] at h2
  apply stepStar_stepPlus_stepPlus h2
  -- Phase 3: R5+R1: (0, 0, 2*d+2, 0, d) →⁺ (2, 0, 2*d, 1, d)
  apply stepPlus_stepStar_stepPlus (open_r5r1 (c := 2 * d) (e := d))
  -- Phase 4: R2+R1+R1 chain (d rounds): (2, 0, 2*d, 1, d) →* (3*d+2, 0, 0, 3*d+1, 0)
  have h4 := r2r1r1_chain (c := 0) d 0 0
  simp only [Nat.zero_add] at h4
  apply stepStar_trans h4
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨d+1, 0, 0, d, 0⟩) 1
  intro d; exists 3 * d + 1; exact main_trans

end Sz22_2003_unofficial_534
