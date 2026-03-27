import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #574: [35/6, 11/2, 4/55, 3/7, 196/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 2  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_574

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | _ => none

-- R4 repeated: transfer d to b
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R1R1R3 chain: n rounds of (R1, R1, R3)
theorem r1r1r3_chain : ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
  have many_step : ∀ k c d e, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- R2R2R3 drain: c rounds of (R2, R2, R3)
theorem r2r2r3_drain : ⟨2, 0, c+k, d, e⟩ [fm]⊢* ⟨2, 0, c, d, e+k⟩ := by
  have many_step : ∀ k c e, ⟨2, 0, c+k, d, e⟩ [fm]⊢* ⟨2, 0, c, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- Main transition: (0, 0, 0, 2*(n+1), n+2) →⁺ (0, 0, 0, 2*(n+2), n+3)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2*(n+1), n+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*(n+2), n+3⟩ := by
  -- Phase 1: R4 chain
  rw [show 2*(n+1) = 0 + 2*(n+1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0) (e := n+2))
  simp only [Nat.zero_add]
  -- Phase 2: R5
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- Phase 3: R1R1R3 chain
  have h3 := @r1r1r3_chain 0 (n+1) 0 2 0
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- Phase 4: R2R2R3 drain
  have h4 := @r2r2r3_drain 0 (n+1) (2+2*(n+1)) 0
  simp only [Nat.zero_add] at h4
  apply stepStar_trans h4
  -- Phase 5: Final R2, R2
  step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2*(n+1), n+2⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩

end Sz22_2003_unofficial_574
