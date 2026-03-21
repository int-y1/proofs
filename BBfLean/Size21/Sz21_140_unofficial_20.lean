import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #20: [28/15, 21/22, 25/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_20

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R4 repeated - convert d to e
theorem d_to_e : ⟨0, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, 0, d⟩ := by
  have many_step : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro c d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  have h := many_step d c 0 0
  simp only [Nat.zero_add] at h
  exact h

-- Phase 5: R3 repeated - convert a to c
theorem a_to_c : ⟨a, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+2*a, d, 0⟩ := by
  have many_step : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a c d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  have h := many_step a 0 c d
  rw [Nat.zero_add] at h
  exact h

-- Phase 4: R2+R1 interleaved chain
-- Implicit order: {a c k d}
-- ⟨a+1, 0, c+k, d, k⟩ →* ⟨a+1+k, 0, c, d+2*k, 0⟩
theorem r2r1_chain : ⟨a+1, 0, c+k, d, k⟩ [fm]⊢* ⟨a+1+k, 0, c, d+2*k, 0⟩ := by
  have many_step : ∀ k a c d, ⟨a+1, 0, c+k, d, k⟩ [fm]⊢* ⟨a+1+k, 0, c, d+2*k, 0⟩ := by
    intro k; induction' k with k h <;> intro a c d
    · exists 0
    show ⟨a+1, 0, c+(k+1), d, k+1⟩ [fm]⊢* ⟨a+1+(k+1), 0, c, d+2*(k+1), 0⟩
    step fm  -- R2
    step fm  -- R1
    apply stepStar_trans (h _ _ _)
    ring_nf; finish
  exact many_step k a c d

-- Main transition: (0, 0, c+d+3, d, 0) →⁺ (0, 0, c+2*d+5, 2*d+1, 0)
theorem main_trans : ⟨0, 0, c+d+3, d, 0⟩ [fm]⊢⁺ ⟨0, 0, c+2*d+5, 2*d+1, 0⟩ := by
  -- Phase 1: d_to_e: →* (0, 0, c+d+3, 0, d)
  apply stepStar_stepPlus_stepPlus d_to_e
  -- Phase 2+3: R5 then R1
  step fm  -- R5: (0, 0, c+d+3, 0, d) → (0, 1, c+d+2, 0, d)
  step fm  -- R1: (0, 1, c+d+2, 0, d) → (2, 0, c+d+1, 1, d)
  -- Now goal is: (2, 0, c+d+1, 1, d) ⊢* (0, 0, c+2*d+5, 2*d+1, 0)
  -- Phase 4: r2r1_chain with a=1, c'=c+1, k=d, d'=1
  -- @r2r1_chain 1 (c+1) d 1 : (2, 0, c+1+d, 1, d) ⊢* (2+d, 0, c+1, 1+2*d, 0)
  apply stepStar_trans (c₂ := ⟨d+2, 0, c+1, 2*d+1, 0⟩)
  · have h4 := @r2r1_chain 1 (c+1) d 1
    simp only [Nat.add_right_comm, Nat.add_comm 1] at h4
    exact h4
  -- Phase 5: a_to_c with a=d+2, c'=c+1, d'=2*d+1
  · have h5 := @a_to_c (d+2) (c+1) (2*d+1)
    -- h5 : (d+2, 0, c+1, 2*d+1, 0) ⊢* (0, 0, c+1+2*(d+2), 2*d+1, 0)
    -- goal: (d+2, 0, c+1, 2*d+1, 0) ⊢* (0, 0, c+2*d+5, 2*d+1, 0)
    simp only [(by ring : c+1+2*(d+2) = c+2*d+5)] at h5
    exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ) (fun ⟨c, d⟩ ↦ ⟨0, 0, c+d+3, d, 0⟩) ⟨0, 1⟩
  intro ⟨c, d⟩
  exists ⟨c+1, 2*d+1⟩
  -- goal: (0, 0, c+d+3, d, 0) ⊢⁺ (0, 0, (c+1)+(2*d+1)+3, 2*d+1, 0)
  -- main_trans: (0, 0, c+d+3, d, 0) ⊢⁺ (0, 0, c+2*d+5, 2*d+1, 0)
  simp only [(by ring : (c+1)+(2*d+1)+3 = c+2*d+5)]
  exact main_trans
