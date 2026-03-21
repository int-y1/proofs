import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #114: [77/15, 26/3, 9/91, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1  0
 1 -1  0  0  0  1
 0  2  0 -1  0 -1
 0  0  1  0 -1  0
-1  1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_114

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- R4 repeated: e → c
theorem e_to_c : ∀ k, ∀ a c f, ⟨a, 0, c, 0, k, f⟩ [fm]⊢* ⟨a, 0, c+k, 0, 0, f⟩ := by
  intro k; induction' k with k h <;> intro a c f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a (c + 1) f)
  ring_nf; finish

-- R1R1R3 chain: each round consumes 2 from c, 1 from f; adds 1 to d, 2 to e
theorem r1r1r3_chain : ∀ k, ∀ a c d e f, ⟨a, 2, c + 2*k, d, e, f + k⟩ [fm]⊢* ⟨a, 2, c, d + k, e + 2*k, f⟩ := by
  intro k; induction' k with k h <;> intro a c d e f
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
      show f + (k + 1) = (f + 1) + k from by ring]
  apply stepStar_trans (h a (c + 2) d e (f + 1))
  rw [show 2 = 1 + 1 from rfl, show c + 2 = (c + 1) + 1 from by ring]
  step fm
  step fm
  step fm
  ring_nf; finish

-- R3R2R2 drain: each round consumes 1 from d, adds 2 to a, 1 to f
theorem drain : ∀ k, ∀ a e f, ⟨a, 0, 0, k, e, f + 1⟩ [fm]⊢* ⟨a + 2*k, 0, 0, 0, e, f + 1 + k⟩ := by
  intro k; induction' k with k h <;> intro a e f
  · exists 0
  step fm
  rw [show 2 = 1 + 1 from rfl]
  step fm
  step fm
  rw [show f + 2 = (f + 1) + 1 from by ring]
  apply stepStar_trans (h (a + 2) e (f + 1))
  ring_nf; finish

-- Main transition for even n: n = 2*m
-- (a+1, 0, 0, 0, 2m+1, 2m+1) ⊢⁺ (a+2m+2, 0, 0, 0, 2m+2, 2m+2)
theorem main_trans_even (m : ℕ) : ∀ a, ⟨a+1, 0, 0, 0, 2*m+1, 2*m+1⟩ [fm]⊢⁺ ⟨a+2*m+2, 0, 0, 0, 2*m+2, 2*m+2⟩ := by
  intro a
  -- Phase 1: R4 (2m+1 times)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 2*m+1, 0, 0, 2*m+1⟩)
  · have h := e_to_c (2*m+1) (a+1) 0 (2*m+1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨a, 1, 2*m+1, 0, 1, 2*m+1⟩)
  · show fm ⟨a+1, 0, 2*m+1, 0, 0, 2*m+1⟩ = some ⟨a, 1, 2*m+1, 0, 1, 2*m+1⟩; simp [fm]
  -- Phase 3: R1 step
  apply stepStar_trans (c₂ := ⟨a, 0, 2*m, 1, 2, 2*m+1⟩)
  · rw [show 2*m+1 = (2*m) + 1 from by ring, show 1 = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- Phase 3b: R3 step
  apply stepStar_trans (c₂ := ⟨a, 2, 2*m, 0, 2, 2*m⟩)
  · rw [show 2*m+1 = (2*m) + 1 from by ring, show 1 = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- Phase 4: R1R1R3 chain (m rounds)
  apply stepStar_trans (c₂ := ⟨a, 2, 0, m, 2+2*m, m⟩)
  · have h := r1r1r3_chain m a 0 0 2 m
    simp only [Nat.zero_add] at h
    rw [show m + m = 2 * m from by ring] at h; exact h
  -- Phase 5: R2R2 tail (b=2, c=0)
  apply stepStar_trans (c₂ := ⟨a+2, 0, 0, m, 2+2*m, m+2⟩)
  · rw [show 2 = 1 + 1 from rfl]
    step fm; step fm; ring_nf; finish
  -- Phase 6: drain m rounds
  apply stepStar_trans (c₂ := ⟨a+2+2*m, 0, 0, 0, 2+2*m, m+2+m⟩)
  · rw [show m + 2 = (m+1) + 1 from by ring]
    exact drain m (a+2) (2+2*m) (m+1)
  -- Close with arithmetic
  ring_nf; finish

-- Main transition for odd n: n = 2*m+1
-- (a+1, 0, 0, 0, 2m+2, 2m+2) ⊢⁺ (a+2m+3, 0, 0, 0, 2m+3, 2m+3)
theorem main_trans_odd (m : ℕ) : ∀ a, ⟨a+1, 0, 0, 0, 2*m+2, 2*m+2⟩ [fm]⊢⁺ ⟨a+2*m+3, 0, 0, 0, 2*m+3, 2*m+3⟩ := by
  intro a
  -- Phase 1: R4 (2m+2 times)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 2*m+2, 0, 0, 2*m+2⟩)
  · have h := e_to_c (2*m+2) (a+1) 0 (2*m+2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step
  apply step_stepStar_stepPlus (c₂ := ⟨a, 1, 2*m+2, 0, 1, 2*m+2⟩)
  · show fm ⟨a+1, 0, 2*m+2, 0, 0, 2*m+2⟩ = some ⟨a, 1, 2*m+2, 0, 1, 2*m+2⟩; simp [fm]
  -- Phase 3: R1 step
  apply stepStar_trans (c₂ := ⟨a, 0, 2*m+1, 1, 2, 2*m+2⟩)
  · rw [show 2*m+2 = (2*m+1) + 1 from by ring, show 1 = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- Phase 3b: R3 step
  apply stepStar_trans (c₂ := ⟨a, 2, 2*m+1, 0, 2, 2*m+1⟩)
  · rw [show 2*m+2 = (2*m+1) + 1 from by ring, show 1 = 0 + 1 from rfl]
    step fm; ring_nf; finish
  -- Phase 4: R1R1R3 chain (m rounds)
  apply stepStar_trans (c₂ := ⟨a, 2, 1, m, 2+2*m, m+1⟩)
  · have h := r1r1r3_chain m a 1 0 2 (m+1)
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * m = 2 * m + 1 from by ring, show m + 1 + m = 2 * m + 1 from by ring] at h
    exact h
  -- Phase 5: R1R2 tail (b=2, c=1)
  apply stepStar_trans (c₂ := ⟨a+1, 0, 0, m+1, 2+2*m+1, m+1+1⟩)
  · rw [show 2 = 1 + 1 from rfl, show 1 = 0 + 1 from rfl]
    step fm; step fm; ring_nf; finish
  -- Phase 6: drain (m+1) rounds
  apply stepStar_trans (c₂ := ⟨a+1+2*(m+1), 0, 0, 0, 2+2*m+1, m+1+1+(m+1)⟩)
  · exact drain (m+1) (a+1) (2+2*m+1) (m+1)
  ring_nf; finish

-- Combined main transition
theorem main_trans : ∀ a n, ⟨a+1, 0, 0, 0, n+1, n+1⟩ [fm]⊢⁺ ⟨a+n+2, 0, 0, 0, n+2, n+2⟩ := by
  intro a n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2m (even)
    rw [show m + m = 2 * m from by ring] at hm; subst hm
    have h := main_trans_even m a
    rw [show a + 2 * m + 2 = a + 2 * m + 2 from rfl] at h; exact h
  · -- n = 2m + 1 (odd)
    subst hm
    have h := main_trans_odd m a
    rw [show a + (2 * m + 1) + 2 = a + 2 * m + 3 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring]; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a+1, 0, 0, 0, n+1, n+1⟩) ⟨1, 1⟩
  intro ⟨a, n⟩; exact ⟨⟨a+n+1, n+1⟩, main_trans a n⟩

end Sz21_140_unofficial_114
