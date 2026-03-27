import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #16: [1/12, 75/2, 2/35, 11/5, 196/11]

Vector representation:
```
-2 -1  0  0  0
-1  1  2  0  0
 1  0 -1 -1  0
 0  0 -1  0  1
 2  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_16

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+2, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+2, e⟩
  | _ => none

-- Phase 3: R3-R2 chain. Each round: (0, b, c+1, d+1, e) -> (1, b, c, d, e) -> (0, b+1, c+2, d, e)
-- Net: b += 1, c += 1, d -= 1
theorem r3r2_chain : ∀ k b c d e, ⟨0, b, c+1, d+k, e⟩ [fm]⊢* ⟨0, b+k, c+k+1, d, e⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Phase 4: R4 chain. Each round: (0, b, c+1, 0, e) -> (0, b, c, 0, e+1)
theorem c_to_e : ∀ k b c e, ⟨0, b, c+k, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro b c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 5: R5-R1 chain. Each round: (0, b+1, 0, d, e+1) -> (2, b+1, 0, d+2, e) -> (0, b, 0, d+2, e)
theorem r5r1_chain : ∀ k b d e, ⟨0, b+k, 0, d, e+k⟩ [fm]⊢* ⟨0, b, 0, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (0, 0, 0, d, e+1) ⊢⁺ (0, 0, 0, 2*d+8, e+2)
theorem main_trans (d e : ℕ) : ⟨0, 0, 0, d, e+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*d+8, e+2⟩ := by
  -- Phase 1: R5
  step fm
  -- (2, 0, 0, d+2, e)
  -- Phase 2: R2, R2
  step fm; step fm
  -- (0, 2, 4, d+2, e)
  -- Phase 3: R3-R2 chain × (d+2)
  apply stepStar_trans (c₂ := ⟨0, d+4, d+6, 0, e⟩)
  · rw [show (4 : ℕ) = 3 + 1 from by ring]
    have h := r3r2_chain (d+2) 2 3 0 e
    simp only [Nat.zero_add, (by ring : 3 + (d + 2) + 1 = d + 6),
               (by ring : 2 + (d + 2) = d + 4)] at h
    exact h
  -- Phase 4: R4 chain × (d+6)
  apply stepStar_trans (c₂ := ⟨0, d+4, 0, 0, e+d+6⟩)
  · have h := c_to_e (d+6) (d+4) 0 e
    simp only [Nat.zero_add, (by ring : e + (d + 6) = e + d + 6)] at h
    exact h
  -- Phase 5: R5-R1 chain × (d+4)
  have h := r5r1_chain (d+4) 0 0 (e+2)
  simp only [Nat.zero_add, (by ring : e + 2 + (d + 4) = e + d + 6),
             (by ring : 0 + 2 * (d + 4) = 2 * d + 8)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d, e+1⟩) ⟨2, 0⟩
  intro ⟨d, e⟩; exact ⟨⟨2*d+8, e+1⟩, main_trans d e⟩

end Sz22_2003_unofficial_16
