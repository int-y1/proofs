import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #55: [1/15, 9/539, 98/3, 5/7, 99/2]

Vector representation:
```
 0 -1 -1  0  0
 0  2  0 -2 -1
 1 -1  0  2  0
 0  0  1 -1  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_55

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- (R3, R2) interleaved chain: k rounds
-- Each round: R3 (a+=1, b-=1, d+=2) then R2 (b+=2, d-=2, e-=1). Net: a+=1, b+=1, e-=1.
theorem r3r2_chain : ∀ k a b, ⟨a, b+1, 0, 0, k⟩ [fm]⊢* ⟨a+k, b+k+1, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  step fm  -- R3: (a+1, b, 0, 2, k+1)
  step fm  -- R2: (a+1, b+2, 0, 0, k)
  rw [show b + 2 = (b + 1) + 1 from by ring]
  apply stepStar_trans (h (a + 1) (b + 1))
  ring_nf; finish

-- R3 chain: b → 0
theorem r3_chain : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a+k, 0, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  step fm
  apply stepStar_trans (h (a + 1) (d + 2))
  ring_nf; finish

-- R4 chain: d → c
theorem d_to_c : ∀ k a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (h a (c + 1))
  ring_nf; finish

-- (R5, R1, R1) chain: k rounds
-- Each round: R5 (a-=1, b+=2, e+=1), R1 (b-=1, c-=1), R1 (b-=1, c-=1). Net: a-=1, c-=2, e+=1.
theorem r5r1r1_chain : ∀ k a e, ⟨a+k, 0, 2*k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  step fm  -- R5: (a+k, 2, 2*k+1+1, 0, e+1) wait, c pattern
  -- Input: ((a+k)+1, 0, (2*k+1)+1, 0, e)
  -- R5 matches a+1 pattern: (a+k, 0+2, (2*k+1)+1, 0, e+1)
  -- = (a+k, 2, 2*k+2, 0, e+1)
  -- R1 matches b+1, c+1: (a+k, 1, 2*k+1, 0, e+1)
  step fm
  -- R1 again: (a+k, 0, 2*k, 0, e+1)
  step fm
  apply stepStar_trans (h a (e + 1))
  ring_nf; finish

-- Main transition: (a+1, 0, 0, 0, e) →⁺ (a+e+1, 0, 0, 0, e+3)
theorem main_trans (a e : ℕ) : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+e+1, 0, 0, 0, e+3⟩ := by
  -- Phase 1: R5: (a+1, 0, 0, 0, e) -> (a, 2, 0, 0, e+1)
  apply step_stepStar_stepPlus (c₂ := ⟨a, 2, 0, 0, e+1⟩)
  · show fm ⟨a+1, 0, 0, 0, e⟩ = some ⟨a, 0+2, 0, 0, e+1⟩; simp [fm]
  -- Phase 2: (R3, R2) chain × (e+1): (a, 2, 0, 0, e+1) -> (a+e+1, e+3, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+e+1, e+3, 0, 0, 0⟩)
  · rw [show (2 : ℕ) = 1 + 1 from rfl]
    have h := r3r2_chain (e + 1) a 1
    rw [show a + (e + 1) = a + e + 1 from by ring,
        show 1 + (e + 1) + 1 = e + 3 from by ring] at h
    exact h
  -- Phase 3: R3 chain × (e+3): (a+e+1, e+3, 0, 0, 0) -> (a+2*e+4, 0, 0, 2*e+6, 0)
  apply stepStar_trans (c₂ := ⟨a+2*e+4, 0, 0, 2*e+6, 0⟩)
  · have h := r3_chain (e + 3) (a + e + 1) 0
    rw [show a + e + 1 + (e + 3) = a + 2 * e + 4 from by ring,
        show 0 + 2 * (e + 3) = 2 * e + 6 from by ring] at h
    exact h
  -- Phase 4: R4 chain (d → c): (a+2*e+4, 0, 0, 2*e+6, 0) -> (a+2*e+4, 0, 2*e+6, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+2*e+4, 0, 2*e+6, 0, 0⟩)
  · have h := d_to_c (2*e+6) (a+2*e+4) 0
    rw [show 0 + (2 * e + 6) = 2 * e + 6 from by ring] at h
    exact h
  -- Phase 5: (R5, R1, R1) chain × (e+3): (a+2*e+4, 0, 2*e+6, 0, 0) -> (a+e+1, 0, 0, 0, e+3)
  have h := r5r1r1_chain (e + 3) (a + e + 1) 0
  rw [show a + e + 1 + (e + 3) = a + 2 * e + 4 from by ring,
      show 2 * (e + 3) = 2 * e + 6 from by ring,
      show 0 + (e + 3) = e + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 3⟩) (by execute fm 21)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a+1, 0, 0, 0, e⟩) ⟨0, 3⟩
  intro ⟨a, e⟩; exact ⟨⟨a+e, e+3⟩, main_trans a e⟩

end Sz22_2003_unofficial_55
