import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1819: [9/10, 55/21, 4/3, 7/11, 33/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  0
 0  0  0  1 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1819

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R2R1 chain: interleaved R2,R1 steps.
-- (a+k, b+1, 0, d+k, e) →* (a, b+k+1, 0, d, e+k)
theorem r2r1_chain : ∀ k a b d e, ⟨a+k, b+1, 0, d+k, e⟩ [fm]⊢* ⟨a, b+k+1, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    ring_nf; finish

-- R3 chain: drain b, adding 2*k to a.
-- (a, k, 0, 0, e) →* (a+2*k, 0, 0, 0, e)
theorem r3_chain : ∀ k a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) e)
    ring_nf; finish

-- R4 chain: move e to d.
-- (a, 0, 0, d, k) →* (a, 0, 0, d+k, 0)
theorem r4_chain : ∀ k a d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih a (d + 1)

-- Main transition: (a + d + 2, 0, 0, d + 1, 0) ⊢⁺ (a + 2*d + 4, 0, 0, d + 2, 0)
theorem main_trans (a d : ℕ) :
    ⟨a + d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 4, 0, 0, d + 2, 0⟩ := by
  -- R5: (a+d+1, 1, 0, d+1, 1)
  rw [show a + d + 2 = a + d + 1 + 1 from by ring]
  step fm
  -- Now at (a+d+1, 1, 0, d+1, 1). Apply R2R1 chain with k=d+1.
  have h1 := r2r1_chain (d + 1) a 0 0 1
  rw [show a + d + 1 = a + (d + 1) from by ring]
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  -- Now at (a, d+1+1, 0, 0, 1+(d+1)).
  rw [show d + 1 + 1 = d + 2 from by ring,
      show 1 + (d + 1) = d + 2 from by ring]
  -- R3 chain: drain b=d+2
  apply stepStar_trans (r3_chain (d + 2) a (d + 2))
  -- Now at (a + 2*(d+2), 0, 0, 0, d+2).
  rw [show a + 2 * (d + 2) = a + 2 * d + 4 from by ring]
  -- R4 chain: move e=d+2 to d
  apply stepStar_trans (r4_chain (d + 2) (a + 2 * d + 4) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, d⟩ ↦ ⟨m + d + 2, 0, 0, d + 1, 0⟩) ⟨0, 0⟩
  intro ⟨m, d⟩
  refine ⟨⟨m + d + 1, d + 1⟩, ?_⟩
  show ⟨m + d + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨m + d + 1 + (d + 1) + 2, 0, 0, (d + 1) + 1, 0⟩
  rw [show m + d + 1 + (d + 1) + 2 = m + 2 * d + 4 from by ring,
      show (d + 1) + 1 = d + 2 from by ring]
  exact main_trans m d
