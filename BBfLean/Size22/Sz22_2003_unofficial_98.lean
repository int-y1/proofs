import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #98: [1/30, 3/77, 245/3, 4/7, 363/2]

Vector representation:
```
-1 -1 -1  0  0
 0  1  0 -1 -1
 0 -1  1  2  0
 2  0  0 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_98

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3+R2+R2 chain: (0, b+1, b, 0, 2*k) ->* (0, b+k+1, b+k, 0, 0)
theorem r3r2r2_chain : ∀ k, ∀ b, ⟨0, b+1, b, 0, 2*k⟩ [fm]⊢* ⟨0, b+k+1, b+k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro b
  · ring_nf; finish
  step fm; step fm; step fm
  apply stepStar_trans (h (b + 1))
  ring_nf; finish

-- R3 drain b register: (0, k, c, d, 0) ->* (0, 0, c+k, d+2*k, 0)
theorem r3_drain : ∀ k, ∀ c d, ⟨0, k, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+k, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4 drain d register: (a, 0, c, k, 0) ->* (a+2*k, 0, c, 0, 0)
theorem r4_drain : ∀ k, ∀ a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a+2*k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R5+R1 chain: each round does R5 then R1, consuming 2 from a and 1 from c
-- (a+2, 0, c+1, 0, e) -> R5 -> (a+1, 1, c+1, 0, e+2) -> R1 -> (a, 0, c, 0, e+2)
theorem r5r1_chain : ∀ k, ∀ a e, ⟨a+2*k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · ring_nf; finish
  rw [show a + 2 * (k + 1) = a + 2 * k + 1 + 1 from by ring]
  step fm
  rw [show a + 2 * k + 1 = a + 2 * k + 1 from rfl]
  step fm
  apply stepStar_trans (h a (e + 2))
  ring_nf; finish

-- Main transition: (2, 0, 0, 0, 2*n) ->+ (2, 0, 0, 0, 2*(2*n+1))
theorem main_trans (n : ℕ) : ⟨2, 0, 0, 0, 2*n⟩ [fm]⊢⁺ ⟨2, 0, 0, 0, 2*(2*n+1)⟩ := by
  -- (2, 0, 0, 0, 2n) -> 5 steps -> (0, 1, 0, 0, 2n)
  step fm; step fm; step fm; step fm; step fm
  -- r3r2r2_chain -> (0, n+1, n, 0, 0)
  have h2 := r3r2r2_chain n 0
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  -- R3 drain -> (0, 0, 2n+1, 2n+2, 0)
  have h3 := r3_drain (n+1) n 0
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- R4 drain -> (4n+4, 0, 2n+1, 0, 0)
  apply stepStar_trans (r4_drain (2*(n+1)) 0 (n+(n+1)))
  -- R5+R1 chain -> (2, 0, 0, 0, 4n+2)
  rw [show 0 + 2 * (2 * (n + 1)) = 2 + 2 * (n + (n + 1)) from by ring,
      show n + (n + 1) = n + (n + 1) from rfl]
  apply stepStar_trans (r5r1_chain (n+(n+1)) 2 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2*3⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2, 0, 0, 0, 2*n⟩) 3
  intro n; exact ⟨2*n+1, main_trans n⟩
