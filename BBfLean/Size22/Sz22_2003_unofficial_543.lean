import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #543: [28/15, 9/44, 25/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-2  2  0  0 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_543

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+2, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, c, d, 0) ->* (a, 0, c+2*k, d, 0)
theorem a_to_c : ∀ k c, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h (c + 2))
  ring_nf; finish

-- R4 chain: (0, 0, c, d+k, e) ->* (0, 0, c, d, e+k)
theorem d_to_e : ∀ k d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h d (e + 1))
  ring_nf; finish

-- R1R1R2 chain: 3 steps per round, all free vars quantified
theorem r1r1r2_chain : ∀ k, ∀ a c d e,
    ⟨a, 2, c+2*k, d, e+k⟩ [fm]⊢* ⟨a+2*k, 2, c, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h (a + 2) c (d + 2) e)
  ring_nf; finish

-- Main transition: (d+2, 0, 0, d+1, 0) ->+ (2*d+4, 0, 0, 2*d+3, 0)
theorem main_trans : ⟨d+2, 0, 0, d+1, 0⟩ [fm]⊢⁺ ⟨2*d+4, 0, 0, 2*d+3, 0⟩ := by
  -- Phase 1: first R3 step for ⊢⁺
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  -- Now at (d+1, 0, 2, d+1, 0). Use show to set goal explicitly.
  show (d + 1, 0, 2, d + 1, 0) [fm]⊢* (2 * d + 4, 0, 0, 2 * d + 3, 0)
  -- Remaining R3 chain: a_to_c with a=0, k=d+1, c=2, d=d+1
  -- Need first component as 0+(d+1)
  have h1 := @a_to_c 0 (d+1) (d+1) 2
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  -- Now at (0, 0, 2+2*(d+1), d+1, 0)
  -- Phase 2: R4 chain: d_to_e with k=d+1, d=0, e=0
  have h2 := @d_to_e (2+2*(d+1)) (d+1) 0 0
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  -- Now at (0, 0, 2+2*(d+1), 0, d+1)
  -- Phase 3: R5, R1, R2 (opening)
  rw [show 2 + 2 * (d + 1) = (2 * d + 3) + 1 from by ring]
  step fm  -- R5: (0, 1, 2*d+3, 0, d+1)
  rw [show 2 * d + 3 = (2 * d + 2) + 1 from by ring]
  step fm  -- R1: (2, 0, 2*d+2, 1, d+1)
  step fm  -- R2: (0, 2, 2*d+2, 1, d)
  -- Phase 4: R1R1R2 chain with k=d rounds
  rw [show 2 * d + 2 = 2 + 2 * d from by ring]
  have h3 := @r1r1r2_chain d 0 2 1 0
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- Now at (2*d, 2, 2, 1+2*d, 0)
  -- Phase 5: R1, R1 (closing)
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
  step fm  -- R1
  step fm  -- R1
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨d+2, 0, 0, d+1, 0⟩) 0
  intro d; exact ⟨2*d+2, main_trans⟩
