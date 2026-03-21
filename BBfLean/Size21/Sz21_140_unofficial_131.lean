import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #131: [9/10, 55/21, 44/3, 7/11, 3/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  1
 0  0  0  1 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_131

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R4 repeated: e → d
theorem e_to_d : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e+k⟩ [fm]⊢* ⟨a, 0, 0, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = e + k + 1 from by ring]
  step fm
  rw [show d + 1 = (d + 1) from rfl]
  apply stepStar_trans (h a (d + 1) e)
  ring_nf; finish

-- Phase 2b: R2+R1 chain: each pair consumes 1 from a and d, produces 1 to b and e
-- k pairs: (a+k, b+1, 0, d+k, e) →* (a, b+1+k, 0, d, e+k)
theorem r2r1_chain : ∀ k, ∀ a b d e, ⟨a+k, b+1, 0, d+k, e⟩ [fm]⊢* ⟨a, b+1+k, 0, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  -- R2: (a+k+1, b+1, 0, d+k+1, e) → (a+k+1, b, 1, d+k, e+1)
  step fm
  -- R1: (a+k+1, b, 1, d+k, e+1) → (a+k, b+2, 0, d+k, e+1)
  step fm
  rw [show b + 2 = (b + 1) + 1 from by ring]
  apply stepStar_trans (h a (b + 1) d (e + 1))
  ring_nf; finish

-- Phase 2 combined: (d+1, 0, 0, d, 0) →* (0, d+1, 0, 0, d) via R5 then d R2+R1 pairs
theorem interleaved_phase : ∀ d, ⟨d+1, 0, 0, d, 0⟩ [fm]⊢* ⟨0, d+1, 0, 0, d⟩ := by
  intro d
  -- R5 step: (d+1, 0, 0, d, 0) → (d, 1, 0, d, 0)
  apply stepStar_trans (c₂ := ⟨d, 1, 0, d, 0⟩)
  · step fm; finish
  -- R2+R1 chain with k=d, a=0, b=0, d=0, e=0: (0+d, 0+1, 0, 0+d, 0) →* (0, 0+1+d, 0, 0, 0+d)
  have h := r2r1_chain d 0 0 0 0
  simp only [Nat.zero_add] at h
  rw [show (0 : ℕ) + 1 + d = d + 1 from by ring] at h
  exact h

-- Phase 3: R3 repeated: b → a,e (when c=0, d=0)
-- Each R3 step: (a, b+1, 0, 0, e) → (a+2, b, 0, 0, e+1)
theorem b_to_ae : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+2*k, b, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h (a + 2) b (e + 1))
  ring_nf; finish

-- Main transition: (e+1, 0, 0, 0, e) →⁺ (2e+2, 0, 0, 0, 2e+1)
theorem main_trans : ∀ e, ⟨e+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨2*e+2, 0, 0, 0, 2*e+1⟩ := by
  intro e
  -- Phase 1: R4 phase: (e+1, 0, 0, 0, e) →* (e+1, 0, 0, e, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨e+1, 0, 0, e, 0⟩)
  · have h := e_to_d e (e + 1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: interleaved: (e+1, 0, 0, e, 0) →* (0, e+1, 0, 0, e)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, e+1, 0, 0, e⟩)
  · exact interleaved_phase e
  -- Phase 3: R3 phase: (0, e+1, 0, 0, e) →⁺ (2(e+1), 0, 0, 0, 2e+1)
  -- Split off one R3 step for stepPlus
  apply step_stepStar_stepPlus (c₂ := ⟨2, e, 0, 0, e+1⟩)
  · show fm ⟨0, e + 1, 0, 0, e⟩ = some ⟨2, e, 0, 0, e + 1⟩
    rw [show e + 1 = e + 1 from rfl]; simp [fm]
  -- (2, e, 0, 0, e+1) →* (2+2e, 0, 0, 0, e+1+e)
  have h := b_to_ae e 2 0 (e + 1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨e+1, 0, 0, 0, e⟩) 1
  intro e; exact ⟨2*e+1, main_trans e⟩
