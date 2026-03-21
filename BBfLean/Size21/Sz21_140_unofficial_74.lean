import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #74: [4/15, 33/14, 65/2, 7/11, 22/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 1  0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_74

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | _ => none

-- Phase 1: R4 repeated: e → d (when a=0, b=0)
theorem e_to_d (c f : ℕ) : ∀ k, ∀ d, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d+k, 0, f⟩ := by
  intro k; induction' k with k h <;> intro d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- Phase 4: R3 repeated: a → c, f (when b=0, d=0)
theorem a_to_cf (e : ℕ) : ∀ k, ∀ a c f, ⟨a+k, 0, c, 0, e, f⟩ [fm]⊢* ⟨a, 0, c+k, 0, e, f+k⟩ := by
  intro k; induction' k with k h <;> intro a c f
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 3: R2,R1 chain: k rounds
-- Each round: (A+1, 0, C+1, D+1, E, F) →R2→ (A, 1, C+1, D, E+1, F) →R1→ (A+2, 0, C, D, E+1, F)
-- Net effect per round: a += 1, c -= 1, d -= 1, e += 1
-- After k rounds from (a+1, 0, (c+1)+k, k, a+1, f): (a+1+k, 0, c+1, 0, a+1+k, f)
theorem r2r1_chain (f : ℕ) : ∀ k, ∀ a c, ⟨a+1, 0, (c+1)+k, k, a+1, f⟩ [fm]⊢* ⟨a+1+k, 0, c+1, 0, a+1+k, f⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show (c + 1) + (k + 1) = ((c + 1) + k) + 1 from by ring,
      show k + 1 = k + 1 from rfl]
  step fm
  step fm
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans (h (a + 1) c)
  ring_nf; finish

-- Main transition: from canonical state to the next
-- (0, 0, n+1, 0, n, f+1) ⊢⁺ (0, 0, n+2, 0, n+1, f+n+1)
theorem main_trans (n f : ℕ) : ⟨0, 0, n+1, 0, n, f+1⟩ [fm]⊢⁺ ⟨0, 0, n+2, 0, n+1, f+n+1⟩ := by
  -- Phase 1: R4 × n: (0, 0, n+1, 0, n, f+1) →* (0, 0, n+1, n, 0, f+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, n, 0, f+1⟩)
  · have h := e_to_d (n+1) (f+1) n 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5: (0, 0, n+1, n, 0, f+1) → (1, 0, n+1, n, 1, f)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, n+1, n, 1, f⟩)
  · show fm ⟨0, 0, n+1, n, 0, f+1⟩ = some ⟨1, 0, n+1, n, 1, f⟩; simp [fm]
  -- Phase 3: R2,R1 chain × n: (1, 0, n+1, n, 1, f) →* (n+1, 0, 1, 0, n+1, f)
  apply stepStar_trans (c₂ := ⟨n+1, 0, 1, 0, n+1, f⟩)
  · have h := r2r1_chain f n 0 0
    simp only [Nat.zero_add] at h
    rw [show (0 + 1) + n = n + 1 from by ring] at h
    exact h
  -- Phase 4: R3 × (n+1): (n+1, 0, 1, 0, n+1, f) →* (0, 0, n+2, 0, n+1, f+n+1)
  have h := a_to_cf (n+1) (n+1) 0 1 f
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, n+1, 0, n, f+1⟩) ⟨0, 0⟩
  intro ⟨n, f⟩; exact ⟨⟨n+1, f+n⟩, main_trans n f⟩
