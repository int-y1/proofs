import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #81: [1/210, 9/55, 10/3, 7/5, 605/2]

Vector representation:
```
-1 -1 -1 -1  0
 0  2 -1  0 -1
 1 -1  1  0  0
 0  0 -1  1  0
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_81

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

-- Canonical form: C(a, d) = (a+d+1, 0, 0, d, 0)
-- Transition: (a, d) → (a+d, d+3)

-- Phase 1: One round of R5→R2→R3→R1: (a+1, 0, 0, d+1, e) →* (a, 0, 0, d, e+1)
theorem r5r2r3r1_one (a d e : ℕ) :
    ⟨a+1, 0, 0, d+1, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+1⟩ := by
  apply stepStar_trans (c₂ := ⟨a, 0, 1, d+1, e+2⟩)
  · apply step_stepStar; show fm ⟨a+1, 0, 0, d+1, e⟩ = _; simp [fm]
  apply stepStar_trans (c₂ := ⟨a, 2, 0, d+1, e+1⟩)
  · apply step_stepStar
    show fm ⟨a, 0, 0+1, d+1, (e+1)+1⟩ = some ⟨a, 0+2, 0, d+1, e+1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨a+1, 1, 1, d+1, e+1⟩)
  · apply step_stepStar; show fm ⟨a, 1+1, 0, d+1, e+1⟩ = _; simp [fm]
  apply step_stepStar
  show fm ⟨a+1, 1, 0+1, d+1, e+1⟩ = some ⟨a, 0, 0, d, e+1⟩; simp [fm]

-- Phase 1 iterated: d rounds
theorem r5r2r3r1_chain : ∀ k, ∀ a e, ⟨a+k, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show (k + 1) = k + 1 from rfl]
  apply stepStar_trans (r5r2r3r1_one (a + k) k e)
  apply stepStar_trans (h a (e + 1))
  ring_nf; finish

-- Phase 3: R3,R2 interleaved chain: (a, b+2, 0, 0, k) →* (a+k, b+k+2, 0, 0, 0)
theorem r3r2_chain : ∀ k, ∀ a b, ⟨a, b+2, 0, 0, k⟩ [fm]⊢* ⟨a+k, b+k+2, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  step fm
  step fm
  rw [show b + 3 = (b + 1) + 2 from by ring]
  apply stepStar_trans (h (a + 1) (b + 1))
  ring_nf; finish

-- Phase 4: R3 chain: (a, k, c, 0, 0) →* (a+k, 0, c+k, 0, 0)
theorem r3_chain : ∀ k, ∀ a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a+k, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm
  apply stepStar_trans (h (a + 1) (c + 1))
  ring_nf; finish

-- Phase 5: R4 chain: (a, 0, k, d, 0) →* (a, 0, 0, d+k, 0)
theorem r4_chain : ∀ k, ∀ a d, ⟨a, 0, k, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show (k + 1) = k + 1 from rfl]
  step fm
  apply stepStar_trans (h a (d + 1))
  ring_nf; finish

-- Main transition: C(a, d) = (a+d+1, 0, 0, d, 0) →⁺ C(a+d, d+3) = (a+2*d+4, 0, 0, d+3, 0)
theorem main_trans (a d : ℕ) :
    ⟨a+d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a+2*d+4, 0, 0, d+3, 0⟩ := by
  -- Phase 1: d rounds of R5,R2,R3,R1: (a+d+1, 0, 0, d, 0) →* (a+1, 0, 0, 0, d)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 0, d⟩)
  · rw [show a + d + 1 = (a + 1) + d from by ring]
    have h := r5r2r3r1_chain d (a+1) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5: (a+1, 0, 0, 0, d) → (a, 0, 1, 0, d+2)
  apply step_stepStar_stepPlus (c₂ := ⟨a, 0, 1, 0, d+2⟩)
  · show fm ⟨a+1, 0, 0, 0, d⟩ = some ⟨a, 0, 1, 0, d+2⟩; simp [fm]
  -- Phase 2b: R2: (a, 0, 1, 0, d+2) → (a, 2, 0, 0, d+1)
  apply stepStar_trans (c₂ := ⟨a, 2, 0, 0, d+1⟩)
  · apply step_stepStar
    show fm ⟨a, 0, 0+1, 0, (d+1)+1⟩ = some ⟨a, 0+2, 0, 0, d+1⟩; simp [fm]
  -- Phase 3: R3,R2 chain (d+1) times: (a, 2, 0, 0, d+1) →* (a+d+1, d+3, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+d+1, d+3, 0, 0, 0⟩)
  · have h := r3r2_chain (d+1) a 0
    simp only [Nat.zero_add] at h
    rw [show d + 1 + 2 = d + 3 from by ring] at h
    rw [show a + (d + 1) = a + d + 1 from by ring] at h
    exact h
  -- Phase 4: R3 chain (d+3) times: (a+d+1, d+3, 0, 0, 0) →* (a+2*d+4, 0, d+3, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+2*d+4, 0, d+3, 0, 0⟩)
  · have h := r3_chain (d+3) (a+d+1) 0
    simp only [Nat.zero_add] at h
    rw [show a + d + 1 + (d + 3) = a + 2 * d + 4 from by ring] at h
    exact h
  -- Phase 5: R4 chain (d+3) times: (a+2*d+4, 0, d+3, 0, 0) →* (a+2*d+4, 0, 0, d+3, 0)
  have h := r4_chain (d+3) (a+2*d+4) 0
  simp only [Nat.zero_add] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a+d+1, 0, 0, d, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩
  refine ⟨⟨a+d, d+3⟩, ?_⟩
  show ⟨a+d+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a+d+(d+3)+1, 0, 0, d+3, 0⟩
  rw [show a + d + (d + 3) + 1 = a + 2 * d + 4 from by ring]
  exact main_trans a d
