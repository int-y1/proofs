import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #472: [28/15, 21/22, 25/2, 11/7, 9/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  1 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_472

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- (R2, R1) interleaved chain: k rounds
theorem r2r1_chain : ∀ k, ∀ a c d, ⟨a+1, 0, c+k, d, k⟩ [fm]⊢* ⟨a+1+k, 0, c, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show a + 1 = a + 1 from rfl]
  step fm
  rw [show (c + k) + 1 = (c + k) + 1 from rfl]
  step fm
  apply stepStar_trans (h (a + 1) c (d + 2))
  ring_nf; finish

-- R3 repeated k times
theorem r3_chain : ∀ k, ∀ c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (h (c + 2) d)
  ring_nf; finish

-- R4 repeated k times
theorem r4_chain : ∀ k, ∀ c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  step fm
  apply stepStar_trans (h c (e + 1))
  ring_nf; finish

-- Main transition: (0, 0, c+e+5, 0, e) →⁺ (0, 0, c+2*e+10, 0, 2*e+2)
theorem main_trans (c e : ℕ) : ⟨0, 0, c+e+5, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c+2*e+10, 0, 2*e+2⟩ := by
  -- R5: (0, 0, c+e+5, 0, e) → (0, 2, c+e+4, 0, e)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2, c+e+4, 0, e⟩)
  · show fm ⟨0, 0, (c+e+4)+1, 0, e⟩ = some ⟨0, 0+2, c+e+4, 0, e⟩
    simp [fm]
  -- R1: (0, 2, c+e+4, 0, e) → (2, 1, c+e+3, 1, e)
  apply stepStar_trans (c₂ := ⟨2, 1, c+e+3, 1, e⟩)
  · rw [show (2 : ℕ) = 0 + 1 + 1 from rfl,
        show c + e + 4 = (c + e + 3) + 1 from by ring]
    step fm; finish
  -- R1: (2, 1, c+e+3, 1, e) → (4, 0, c+e+2, 2, e)
  apply stepStar_trans (c₂ := ⟨4, 0, c+e+2, 2, e⟩)
  · rw [show c + e + 3 = (c + e + 2) + 1 from by ring]
    step fm; finish
  -- (R2, R1) x e: (4, 0, c+e+2, 2, e) → (4+e, 0, c+2, 2+2*e, 0)
  apply stepStar_trans (c₂ := ⟨4+e, 0, c+2, 2+2*e, 0⟩)
  · have h := r2r1_chain e 3 (c+2) 2
    rw [show 3 + 1 = 4 from rfl, show 3 + 1 + e = 4 + e from by ring] at h
    rw [show c + 2 + e = c + e + 2 from by ring] at h
    exact h
  -- R3 x (4+e): (4+e, 0, c+2, 2+2*e, 0) → (0, 0, c+2*e+10, 2+2*e, 0)
  apply stepStar_trans (c₂ := ⟨0, 0, c+2*e+10, 2+2*e, 0⟩)
  · have h := r3_chain (4+e) (c+2) (2+2*e)
    rw [show c + 2 + 2 * (4 + e) = c + 2 * e + 10 from by ring] at h
    exact h
  -- R4 x (2+2*e): (0, 0, c+2*e+10, 2+2*e, 0) → (0, 0, c+2*e+10, 0, 2+2*e)
  have h := r4_chain (2+2*e) (c+2*e+10) 0
  rw [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 7, 0, 2⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, e⟩ ↦ ⟨0, 0, c+e+5, 0, e⟩) ⟨0, 2⟩
  intro ⟨c, e⟩
  refine ⟨⟨c+3, 2*e+2⟩, ?_⟩
  show ⟨0, 0, c+e+5, 0, e⟩ [fm]⊢⁺ ⟨0, 0, (c+3)+(2*e+2)+5, 0, 2*e+2⟩
  have : (c + 3) + (2 * e + 2) + 5 = c + 2 * e + 10 := by ring
  rw [this]
  exact main_trans c e
