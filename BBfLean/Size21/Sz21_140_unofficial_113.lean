import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #113: [77/15, 2/3, 9/14, 5/11, 99/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  0  0
-1  2  0 -1  0
 0  0  1  0 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_113

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- Phase 1: R4 repeated: e → c (when b=0, d=0)
theorem e_to_c : ∀ k, ∀ a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a (c + 1))
  ring_nf; finish

-- Phase 3: R1R1R3 chain: k rounds
-- Each round: a decreases by 1, c decreases by 2, d increases by 1, e increases by 2
-- (a+k, 2, c+2*k, d, e) →* (a, 2, c, d+k, e+2*k)
theorem r1r1r3_chain : ∀ k, ∀ a c d e, ⟨a + k, 2, c + 2 * k, d, e⟩ [fm]⊢* ⟨a, 2, c, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h a c (d + 1) (e + 2))
  ring_nf; finish

-- Phase 4: R3R2R2 drain: k rounds from (a+1, 0, 0, k, e) → (a+1+k, 0, 0, 0, e)
theorem r3r2r2_drain : ∀ k, ∀ a e, ⟨a + 1, 0, 0, k, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  step fm; step fm; step fm
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans (h (a + 1) e)
  ring_nf; finish

-- Main transition for even n: n = 2*m
-- (2*m+1, 0, 0, 0, 2*m) →⁺ (2*m+2, 0, 0, 0, 2*m+1)
theorem main_trans_even (m : ℕ) : ⟨2*m + 1, 0, 0, 0, 2*m⟩ [fm]⊢⁺ ⟨2*m + 2, 0, 0, 0, 2*m + 1⟩ := by
  -- Phase 1: e_to_c: (2m+1, 0, 0, 0, 2m) →* (2m+1, 0, 2m, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2*m + 1, 0, 2*m, 0, 0⟩)
  · have h := e_to_c (2*m) (2*m + 1) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5: (2m+1, 0, 2m, 0, 0) → (2m, 2, 2m, 0, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨2*m, 2, 2*m, 0, 1⟩)
  · show fm ⟨2*m + 1, 0, 2*m, 0, 0⟩ = some ⟨2*m, 2, 2*m, 0, 1⟩
    simp [fm]
  -- Phase 3: R1R1R3 chain: m rounds
  -- (m+m, 2, 0+2*m, 0, 1) →* (m, 2, 0, 0+m, 1+2*m)
  apply stepStar_trans (c₂ := ⟨m, 2, 0, m, 2*m + 1⟩)
  · have h := r1r1r3_chain m m 0 0 1
    rw [show m + m = 2 * m from by ring,
        show 0 + 2 * m = 2 * m from by ring,
        show 0 + m = m from by ring,
        show 1 + 2 * m = 2 * m + 1 from by ring] at h
    exact h
  -- Phase 3b: R2R2: (m, 2, 0, m, 2m+1) → (m+2, 0, 0, m, 2m+1)
  -- b=2, c=0 → R2,R2
  apply stepStar_trans (c₂ := ⟨m + 2, 0, 0, m, 2*m + 1⟩)
  · step fm; step fm; finish
  -- Phase 4: R3R2R2 drain: m rounds
  -- (m+2, 0, 0, m, 2m+1) = ((m+1)+1, 0, 0, m, 2m+1) → ((m+1)+1+m, 0, 0, 0, 2m+1)
  have h := r3r2r2_drain m (m + 1) (2*m + 1)
  rw [show m + 1 + 1 = m + 2 from by ring,
      show m + 1 + 1 + m = 2*m + 2 from by ring] at h
  refine stepStar_trans h ?_
  finish

-- Main transition for odd n: n = 2*m+1
-- (2*m+2, 0, 0, 0, 2*m+1) →⁺ (2*m+3, 0, 0, 0, 2*m+2)
theorem main_trans_odd (m : ℕ) : ⟨2*m + 2, 0, 0, 0, 2*m + 1⟩ [fm]⊢⁺ ⟨2*m + 3, 0, 0, 0, 2*m + 2⟩ := by
  -- Phase 1: e_to_c
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2*m + 2, 0, 2*m + 1, 0, 0⟩)
  · have h := e_to_c (2*m + 1) (2*m + 2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5: (2m+2, 0, 2m+1, 0, 0) → (2m+1, 2, 2m+1, 0, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨2*m + 1, 2, 2*m + 1, 0, 1⟩)
  · show fm ⟨2*m + 2, 0, 2*m + 1, 0, 0⟩ = some ⟨2*m + 1, 2, 2*m + 1, 0, 1⟩
    simp [fm]
  -- Phase 3: R1R1R3 chain: m rounds
  -- ((m+1)+m, 2, 1+2*m, 0, 1) →* (m+1, 2, 1, 0+m, 1+2*m)
  apply stepStar_trans (c₂ := ⟨m + 1, 2, 1, m, 2*m + 1⟩)
  · have h := r1r1r3_chain m (m + 1) 1 0 1
    convert h using 2; ring_nf
  -- Now: (m+1, 2, 1, m, 2m+1). c=1, b=2. R1 fires.
  -- R1: (m+1, 1, 0, m+1, 2m+2)
  apply stepStar_trans (c₂ := ⟨m + 1, 1, 0, m + 1, 2*m + 2⟩)
  · step fm; ring_nf; finish
  -- R2: (m+2, 0, 0, m+1, 2m+2)
  apply stepStar_trans (c₂ := ⟨m + 2, 0, 0, m + 1, 2*m + 2⟩)
  · step fm; finish
  -- Phase 4: R3R2R2 drain: m+1 rounds
  -- ((m+1)+1, 0, 0, m+1, 2m+2) → ((m+1)+1+(m+1), 0, 0, 0, 2m+2)
  have h := r3r2r2_drain (m + 1) (m + 1) (2*m + 2)
  rw [show m + 1 + 1 = m + 2 from by ring,
      show m + 1 + 1 + (m + 1) = 2*m + 3 from by ring] at h
  refine stepStar_trans h ?_
  finish

-- Main transition: (n+1, 0, 0, 0, n) →⁺ (n+2, 0, 0, 0, n+1)
theorem main_trans (n : ℕ) : ⟨n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, n + 1⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2m (even)
    subst hm
    rw [show m + m = 2 * m from by ring]
    exact main_trans_even m
  · -- n = 2m + 1 (odd)
    subst hm
    exact main_trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n + 1, 0, 0, 0, n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
