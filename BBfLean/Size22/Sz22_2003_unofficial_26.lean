import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #26: [1/15, 196/3, 9/385, 5/7, 33/2]

Vector representation:
```
 0 -1 -1  0  0
 2 -1  0  2  0
 0  2 -1 -1 -1
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_26

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: d to c
theorem d_to_c : ∀ k, ∀ c d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R5+R1 repeated: drain a,c to e
theorem ac_drain : ∀ k, ∀ a e, ⟨a+k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- Pivot: R5 then R2
theorem pivot : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+2, 0, 0, 2, e+1⟩ := by
  step fm; step fm; finish

-- One 4-step round: R4,R3,R2,R2
theorem one_round : ⟨a, 0, 0, d+2, e+1⟩ [fm]⊢* ⟨a+4, 0, 0, d+4, e⟩ := by
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- R4,R3,R2,R2 chain: k rounds
theorem r4r3r2r2_chain : ∀ k, ∀ a d e, ⟨a, 0, 0, d+2, e+k⟩ [fm]⊢* ⟨a+4*k, 0, 0, d+2*k+2, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  apply stepStar_trans (one_round (a := a) (d := d) (e := e + k))
  rw [show d + 4 = (d + 2) + 2 from by ring]
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- Main transition
theorem main_trans (m d : ℕ) : ⟨m+d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨m+4*d+6, 0, 0, 2*d+4, 0⟩ := by
  -- Phase 1: d_to_c: (m+d+1, 0, 0, d, 0) ⊢* (m+d+1, 0, d, 0, 0)
  rw [show (d : ℕ) = 0 + d from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c d 0 0)
  simp only [Nat.zero_add]
  -- Phase 2: ac_drain: (m+d+1, 0, d, 0, 0) ⊢* (m+1, 0, 0, 0, d)
  rw [show m + d + 1 = (m + 1) + d from by ring]
  apply stepStar_stepPlus_stepPlus (ac_drain d (m + 1) 0)
  simp only [Nat.zero_add]
  -- Phase 3: pivot: (m+1, 0, 0, 0, d) ⊢⁺ (m+2, 0, 0, 2, d+1)
  rw [show m + 1 = m + 1 from rfl]
  apply stepPlus_stepStar_stepPlus (@pivot m d)
  -- Phase 4: r4r3r2r2_chain with k = d+1 rounds
  rw [show d + 1 = 0 + (d + 1) from by ring]
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (r4r3r2r2_chain (d + 1) (m + 2) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨6, 0, 0, 4, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, d⟩ ↦ ⟨m+d+1, 0, 0, d, 0⟩) ⟨1, 4⟩
  intro ⟨m, d⟩
  refine ⟨⟨m+2*d+1, 2*d+4⟩, ?_⟩
  simp only []
  rw [show (m + 2 * d + 1) + (2 * d + 4) + 1 = m + 4 * d + 6 from by ring]
  exact main_trans m d

end Sz22_2003_unofficial_26
