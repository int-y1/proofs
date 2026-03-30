import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #901: [4/15, 3/14, 275/2, 7/11, 1/3, 3/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0  0  1 -1
 0 -1  0  0  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_901

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2+R1 chain: each round a += 1, c -= 1, d -= 1
theorem r2r1_chain : ∀ k, ∀ a c, ⟨a+1, 0, c+k, k, 0⟩ [fm]⊢* ⟨a+1+k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) c)
    ring_nf; finish

-- R3 chain: convert a to c and e
theorem r3_chain : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 2) (e + 1))
    ring_nf; finish

-- R4 chain: convert e to d
theorem e_to_d : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

-- Main transition: (0, 0, s+d+3, d+1, 0) ⊢⁺ (0, 0, s+2*d+6, d+3, 0)
theorem main_trans (s d : ℕ) : ⟨0, 0, s + d + 3, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, s + 2 * d + 6, d + 3, 0⟩ := by
  -- R6: (0, 1, s+d+2, d+1, 0)
  step fm
  -- R1: (2, 0, s+d+1, d+1, 0)
  step fm
  -- R2+R1 chain: (2, 0, s+d+1, d+1, 0) ⊢* (d+3, 0, s, 0, 0)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show s + d + 1 = s + (d + 1) from by ring]
  apply stepStar_trans (r2r1_chain (d + 1) 1 s)
  -- R3 chain: (d+3, 0, s, 0, 0) ⊢* (0, 0, s+2*(d+3), 0, d+3)
  rw [show 1 + 1 + (d + 1) = d + 3 from by ring]
  apply stepStar_trans (r3_chain (d + 3) s 0)
  -- R4 chain: (0, 0, s+2*(d+3), 0, d+3) ⊢* (0, 0, s+2*(d+3), d+3, 0)
  rw [show (0 : ℕ) + (d + 3) = d + 3 from by ring]
  apply stepStar_trans (e_to_d (d + 3) (s + 2 * (d + 3)) 0)
  rw [show (0 : ℕ) + (d + 3) = d + 3 from by ring,
      show s + 2 * (d + 3) = s + 2 * d + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 3, 0⟩) (by execute fm 12)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨s, d⟩ ↦ ⟨0, 0, s + d + 3, d + 1, 0⟩) ⟨0, 2⟩
  intro ⟨s, d⟩
  refine ⟨⟨s + d + 1, d + 2⟩, ?_⟩
  show ⟨0, 0, s + d + 3, d + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, s + d + 1 + (d + 2) + 3, (d + 2) + 1, 0⟩
  have h := main_trans s d
  rw [show s + 2 * d + 6 = s + d + 1 + (d + 2) + 3 from by ring,
      show d + 3 = (d + 2) + 1 from by ring] at h
  exact h
