import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #634: [35/6, 143/2, 4/55, 3/7, 28/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 2  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_634

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
    intro k; induction' k with k ih <;> intro b
    · exists 0
    rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish
  exact many_step k b

-- R3R2R2 drain: c rounds converting c to e+1,f+2 each
theorem drain : ⟨0, 0, c + k, d, e + 1, f⟩ [fm]⊢* ⟨0, 0, c, d, e + k + 1, f + 2 * k⟩ := by
  have many_step : ∀ k c e f, ⟨0, 0, c + k, d, e + 1, f⟩ [fm]⊢* ⟨0, 0, c, d, e + k + 1, f + 2 * k⟩ := by
    intro k; induction' k with k ih <;> intro c e f
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish
  exact many_step k c e f

-- R1R1R3 chain: k rounds each consuming 2 from b, adding 1 to c and 2 to d
theorem r1r1r3_chain : ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
  have many_step : ∀ k c d e, ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
    intro k; induction' k with k ih <;> intro c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish
  exact many_step k c d e

-- Even case: from (2, 2k, 0, 1, e+k, f) to (0, 0, 0, 2k+1, e+k+2, f+2k+2)
theorem even_interleave : ⟨2, 2 * k, 0, 1, e + k, f⟩ [fm]⊢* ⟨0, 0, 0, 2 * k + 1, e + k + 2, f + 2 * k + 2⟩ := by
  -- k rounds of R1,R1,R3
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans r1r1r3_chain
  simp only [Nat.zero_add]
  -- now at (2, 0, k, 2k+1, e, f)
  -- R2, R2
  step fm; step fm
  -- now at (0, 0, k, 2k+1, e+2, f+2)
  -- drain k rounds
  rw [show k = 0 + k from by ring]
  apply stepStar_trans drain
  ring_nf; finish

-- Odd case: from (2, 2k+1, 0, 1, e+k, f) to (0, 0, 0, 2k+2, e+k+2, f+2k+3)
theorem odd_interleave : ⟨2, 2 * k + 1, 0, 1, e + k, f⟩ [fm]⊢* ⟨0, 0, 0, 2 * k + 2, e + k + 2, f + 2 * k + 3⟩ := by
  -- k rounds of R1,R1,R3
  rw [show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans r1r1r3_chain
  -- now at (2, 1, k, 2k+1, e, f)
  -- R1: (1, 0, k+1, 2k+2, e, f)
  step fm
  -- R2: (0, 0, k+1, 2k+2, e+1, f+1)
  step fm
  -- drain k+1 rounds
  rw [show 0 + k + 1 = 0 + (k + 1) from by ring, show e + 1 = (e + 0) + 1 from by ring]
  apply stepStar_trans drain
  ring_nf; finish

-- Main transition: canonical state to next canonical state
theorem main_trans (n f : ℕ) : ⟨0, 0, 0, n, 2 * n + 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, 2 * n + 3, f + n + 2⟩ := by
  -- Phase 1: d_to_b (n steps of R4)
  rw [show n = 0 + n from by ring]
  apply stepStar_stepPlus_stepPlus d_to_b
  simp only [Nat.zero_add]
  -- Phase 2: R5 step, giving (2, n, 0, 1, 2n+1, f)
  rw [show f + 1 = f + 1 from rfl]
  step fm
  -- Now at (2, n, 0, 1, 2n+1, f)
  -- Phase 3: split on parity of n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n even: n = k + k
    subst hk
    rw [show 2 * (k + k) + 1 = (3 * k + 1) + k from by ring,
        show k + k = 2 * k from by ring]
    apply stepStar_trans even_interleave
    ring_nf; finish
  · -- n odd: n = 2k + 1
    subst hk
    rw [show 2 * (2 * k + 1) + 1 = (3 * k + 3) + k from by ring]
    apply stepStar_trans odd_interleave
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, 0, n, 2 * n + 1, f + 1⟩) ⟨0, 0⟩
  intro ⟨n, f⟩; exact ⟨⟨n + 1, f + n + 1⟩, main_trans n f⟩
