import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #883: [4/15, 11319/2, 1/147, 5/7, 3/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  3  1
 0 -1  0 -2  0
 0  0  1 -1  0
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_883

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+3, e+1⟩
  | ⟨a, b+1, c, d+2, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: d to c transfer. (0, 0, c, d+k, e) →* (0, 0, c+k, d, e)
theorem d_to_c : ∀ k c d, ⟨(0 : ℕ), 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R2 chain: (a+k, b, 0, d, e) →* (a, b+k, 0, d+3*k, e+k) when c=0
theorem r2_chain : ∀ k a b d e, ⟨a + k, b, 0, d, e⟩ [fm]⊢* ⟨a, b + k, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (d + 3) (e + 1))
    ring_nf; finish

-- R3 chain: (0, b+k, 0, d+2*k, e) →* (0, b, 0, d, e)
theorem r3_chain : ∀ k b d, ⟨(0 : ℕ), b + k, 0, d + 2 * k, e⟩ [fm]⊢* ⟨0, b, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    exact ih b d

-- R1+R2 interleave: (a, 1, k+1, d, e) →* (a+k+2, 0, 0, d+3*k, e+k)
theorem r1r2_interleave : ∀ k a d e, ⟨a, 1, k + 1, d, e⟩ [fm]⊢* ⟨a + k + 2, 0, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · step fm; ring_nf; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) (d + 3) (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, D+2, E+1) ⊢⁺ (0, 0, 0, 4*D+6, E+2*D+4)
theorem main_trans (D E : ℕ) : ⟨(0 : ℕ), 0, 0, D + 2, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * D + 6, E + 2 * D + 4⟩ := by
  -- Phase 1: R4 chain (D+2 steps): →* (0, 0, D+2, 0, E+1)
  rw [show D + 2 = 0 + (D + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (D + 2) 0 0 (e := E + 1))
  rw [show 0 + (D + 2) = D + 2 from by ring]
  -- Phase 2: R5 step: → (0, 1, D+2, 0, E)
  step fm
  -- Phase 3: R1+R2 interleave
  rw [show D + 2 = (D + 1) + 1 from by ring]
  apply stepStar_trans (r1r2_interleave (D + 1) 0 0 E)
  rw [show 0 + (D + 1) + 2 = D + 3 from by ring,
      show 0 + 3 * (D + 1) = 3 * D + 3 from by ring,
      show E + (D + 1) = E + D + 1 from by ring]
  -- Phase 4: R2 chain (D+3 steps)
  rw [show D + 3 = 0 + (D + 3) from by ring]
  apply stepStar_trans (r2_chain (D + 3) 0 0 (3 * D + 3) (E + D + 1))
  rw [show 0 + (D + 3) = D + 3 from by ring,
      show 3 * D + 3 + 3 * (D + 3) = 6 * D + 12 from by ring,
      show E + D + 1 + (D + 3) = E + 2 * D + 4 from by ring]
  -- Phase 5: R3 chain (D+3 steps)
  rw [show D + 3 = 0 + (D + 3) from by ring,
      show 6 * D + 12 = (4 * D + 6) + 2 * (D + 3) from by ring]
  exact r3_chain (D + 3) 0 (4 * D + 6) (e := E + 2 * D + 4)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨D, E⟩ ↦ ⟨0, 0, 0, D + 2, E + 1⟩) ⟨0, 1⟩
  intro ⟨D, E⟩
  exact ⟨⟨4 * D + 4, E + 2 * D + 3⟩, main_trans D E⟩

end Sz22_2003_unofficial_883
