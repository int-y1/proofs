import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #11: [1/45, 7/5, 50/77, 3/7, 605/2]

Vector representation:
```
 0 -2 -1  0  0
 0  0 -1  1  0
 1  0  2 -1 -1
 0  1  0 -1  0
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_11

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

-- r3r2r2_b0: R3,R2,R2 chain with b=0
theorem r3r2r2_b0 : ⟨a, 0, 0, d+1, k⟩ [fm]⊢* ⟨a+k, 0, 0, d+1+k, 0⟩ := by
  have many_step : ∀ k, ∀ a d, ⟨a, 0, 0, d+1, k⟩ [fm]⊢* ⟨a+k, 0, 0, d+1+k, 0⟩ := by
    intro k; induction' k with k h <;> intro a d
    · exists 0
    rw [show d + 1 + (k + 1) = (d + 1 + k) + 1 from by ring]
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a d

-- r3r2r2_b1: R3,R2,R2 chain with b=1
theorem r3r2r2_b1 : ⟨a, 1, 0, d+1, k⟩ [fm]⊢* ⟨a+k, 1, 0, d+1+k, 0⟩ := by
  have many_step : ∀ k, ∀ a d, ⟨a, 1, 0, d+1, k⟩ [fm]⊢* ⟨a+k, 1, 0, d+1+k, 0⟩ := by
    intro k; induction' k with k h <;> intro a d
    · exists 0
    rw [show d + 1 + (k + 1) = (d + 1 + k) + 1 from by ring]
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a d

-- d_to_b: move d to b
theorem d_to_b : ⟨a, b, 0, d+k, 0⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
  have many_step : ∀ k, ∀ b d, ⟨a, b, 0, d+k, 0⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- r5r1_even: R5/R1 chain for even b
theorem r5r1_even : ⟨a+k, 2*k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
  have many_step : ∀ k, ∀ a e, ⟨a+k, 2*k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a e

-- r5r1_odd: R5/R1 chain for odd b
theorem r5r1_odd : ⟨a+k, 2*k+1, 0, 0, e⟩ [fm]⊢* ⟨a, 1, 0, 0, e+2*k⟩ := by
  have many_step : ∀ k, ∀ a e, ⟨a+k, 2*k+1, 0, 0, e⟩ [fm]⊢* ⟨a, 1, 0, 0, e+2*k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a e

-- main_trans: full cycle
theorem main_trans (A : ℕ) (E : ℕ) : ⟨A+1, 0, 0, 0, 2*E⟩ [fm]⊢⁺ ⟨A+1+2*E, 0, 0, 0, 2*E+6⟩ := by
  -- Phase 1: R5 then R2
  apply step_stepStar_stepPlus (c₂ := ⟨A, 0, 1, 0, 2*E+2⟩)
  · show fm ⟨A+1, 0, 0, 0, 2*E⟩ = some ⟨A, 0, 1, 0, 2*E+2⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨A, 0, 0, 1, 2*E+2⟩)
  · step fm; finish
  -- Phase 2: r3r2r2_b0
  apply stepStar_trans (c₂ := ⟨A+2*E+2, 0, 0, 2*E+3, 0⟩)
  · have h := @r3r2r2_b0 A 0 (2*E+2)
    rw [show 0 + 1 = 1 from rfl, show 0 + 1 + (2 * E + 2) = 2 * E + 3 from by ring,
        show A + (2 * E + 2) = A + 2 * E + 2 from by ring] at h
    exact h
  -- Phase 3: d_to_b
  apply stepStar_trans (c₂ := ⟨A+2*E+2, 2*E+3, 0, 0, 0⟩)
  · have h := @d_to_b (A+2*E+2) 0 0 (2*E+3)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 4: r5r1_odd
  apply stepStar_trans (c₂ := ⟨A+E+1, 1, 0, 0, 2*E+2⟩)
  · have h := @r5r1_odd (A+E+1) (E+1) 0
    rw [show A + E + 1 + (E + 1) = A + 2 * E + 2 from by ring,
        show 2 * (E + 1) + 1 = 2 * E + 3 from by ring,
        show 0 + 2 * (E + 1) = 2 * E + 2 from by ring] at h
    exact h
  -- Phase 5: R5 then R2
  apply stepStar_trans (c₂ := ⟨A+E, 1, 1, 0, 2*E+4⟩)
  · rw [show A + E + 1 = (A + E) + 1 from by ring]
    step fm; finish
  apply stepStar_trans (c₂ := ⟨A+E, 1, 0, 1, 2*E+4⟩)
  · step fm; finish
  -- Phase 6: r3r2r2_b1
  apply stepStar_trans (c₂ := ⟨A+3*E+4, 1, 0, 2*E+5, 0⟩)
  · have h := @r3r2r2_b1 (A+E) 0 (2*E+4)
    rw [show 0 + 1 = 1 from rfl, show 0 + 1 + (2 * E + 4) = 2 * E + 5 from by ring,
        show A + E + (2 * E + 4) = A + 3 * E + 4 from by ring] at h
    exact h
  -- Phase 7: d_to_b
  apply stepStar_trans (c₂ := ⟨A+3*E+4, 2*E+6, 0, 0, 0⟩)
  · have h := @d_to_b (A+3*E+4) 1 0 (2*E+5)
    rw [show 1 + (2 * E + 5) = 2 * E + 6 from by ring,
        show 0 + (2 * E + 5) = 2 * E + 5 from by ring] at h
    exact h
  -- Phase 8: r5r1_even
  have h := @r5r1_even (A+1+2*E) (E+3) 0
  rw [show A + 1 + 2 * E + (E + 3) = A + 3 * E + 4 from by ring,
      show 2 * (E + 3) = 2 * E + 6 from by ring] at h
  convert h using 1
  ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 6⟩) (by execute fm 38)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, E⟩ ↦ ⟨A+1, 0, 0, 0, 2*E⟩) ⟨0, 3⟩
  intro ⟨A, E⟩
  refine ⟨⟨A+2*E, E+3⟩, ?_⟩
  show ⟨A+1, 0, 0, 0, 2*E⟩ [fm]⊢⁺ ⟨A+2*E+1, 0, 0, 0, 2*(E+3)⟩
  have h := main_trans A E
  convert h using 2; ring_nf
