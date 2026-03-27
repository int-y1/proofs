import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #34: [1/15, 3/14, 28/33, 605/2, 21/5]

Vector representation:
```
 0 -1 -1  0  0
-1  1  0 -1  0
 2 -1  0  1 -1
-1  0  1  0  2
 0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_34

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: (a+k, 0, c, 0, e) →* (a, 0, c+k, 0, e+2*k)
theorem r4_chain : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a (c + 1) (e + 2)); ring_nf; finish

-- R5/R1 interleave: (0, 0, 2*k+1, d, e) →* (0, 1, 0, d+k+1, e)
theorem r5r1_chain : ∀ k, ∀ d e, ⟨0, 0, 2*k+1, d, e⟩ [fm]⊢* ⟨0, 1, 0, d+k+1, e⟩ := by
  intro k; induction' k with k h <;> intro d e
  · step fm; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (h (d + 1) e); ring_nf; finish

-- R3/R2/R2 drain
theorem r3r2r2_chain : ∀ k, ∀ b d e, ⟨0, b+1, 0, d+k, e+k+1⟩ [fm]⊢* ⟨0, b+1+k, 0, d, e+1⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h (b + 1) d e); ring_nf; finish

-- R3/R2 chain
theorem r3r2_chain : ∀ k, ∀ a b e, ⟨a, b+1, 0, 0, e+k⟩ [fm]⊢* ⟨a+k, b+1, 0, 0, e⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h (a + 1) b e); ring_nf; finish

-- Tail step: 6 steps R4, R1, R3, R2, R3, R2
theorem tail_step : ∀ a b, ⟨a+1, b+2, 0, 0, 0⟩ [fm]⊢* ⟨a+2, b+1, 0, 0, 0⟩ := by
  intro a b; execute fm 6

-- Tail chain
theorem tail_chain : ∀ k, ∀ a b, ⟨a+1+k, b+1+k, 0, 0, 0⟩ [fm]⊢* ⟨a+1+2*k, b+1, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  -- LHS: (a+1+(k+1), b+1+(k+1), 0, 0, 0) = (a+k+2, b+k+2, 0, 0, 0)
  -- tail_step (a+k+1) (b+k): (a+k+1+1, b+k+2, 0, 0, 0) →* (a+k+1+2, b+k+1, 0, 0, 0)
  -- = (a+k+2, b+k+2, ...) →* (a+k+3, b+k+1, ...)
  rw [show a + 1 + (k + 1) = (a + k + 1) + 1 from by ring,
      show b + 1 + (k + 1) = (b + k) + 2 from by ring]
  apply stepStar_trans (tail_step (a + k + 1) (b + k))
  -- now: (a+k+1+2, (b+k)+1, 0, 0, 0) →* (a+1+2*(k+1), b+1, 0, 0, 0)
  -- = (a+k+3, b+k+1, 0, 0, 0) →* (a+2*k+3, b+1, 0, 0, 0)
  -- h (a+2) b: (a+2+1+k, b+1+k, 0, 0, 0) →* (a+2+1+2*k, b+1, 0, 0, 0)
  -- = (a+k+3, b+k+1, 0, 0, 0) →* (a+2*k+3, b+1, 0, 0, 0)
  rw [show a + k + 1 + 2 = (a + 2) + 1 + k from by ring,
      show (b + k) + 1 = b + 1 + k from by ring]
  apply stepStar_trans (h (a + 2) b); ring_nf; finish

-- Tail end: 2 steps R4, R1
theorem tail_end : ⟨a+1, 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a, 0, 0, 0, 2⟩ := by
  execute fm 2

-- Main transition: (2*n+1, 0, 0, 0, 2) →⁺ (4*n+3, 0, 0, 0, 2)
theorem main_trans (n : ℕ) : ⟨2*n+1, 0, 0, 0, 2⟩ [fm]⊢⁺ ⟨4*n+3, 0, 0, 0, 2⟩ := by
  -- Phase 1: R4 chain (2n+1 steps)
  -- (2*n+1, 0, 0, 0, 2) →* (0, 0, 2*n+1, 0, 4*n+4)
  rw [show 2*n+1 = 0 + (2*n+1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2*n+1) 0 0 2)
  simp only [Nat.zero_add]
  -- State: (0, 0, 2*n+1, 0, 2+2*(2*n+1))
  -- Phase 2: R5/R1 interleave
  -- (0, 0, 2*n+1, 0, 4*n+4) →* (0, 1, 0, n+1, 4*n+4)
  apply stepStar_stepPlus_stepPlus (r5r1_chain n 0 (2 + 2 * (2 * n + 1)))
  simp only [Nat.zero_add]
  -- State: (0, 1, 0, n+1, 2+2*(2*n+1))
  -- Phase 3A: R3/R2/R2 drain (n+1 rounds)
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show 2 + 2 * (2 * n + 1) = (3 * n + 2) + (n + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (r3r2r2_chain (n+1) 0 0 (3*n+2))
  -- State: (0, 0+1+(n+1), 0, 0, (3*n+2)+1) = (0, n+2, 0, 0, 3*n+3)
  rw [show 0 + 1 + (n + 1) = (n + 1) + 1 from by ring,
      show 3 * n + 2 + 1 = 0 + (3 * n + 3) from by ring]
  -- Phase 3B: R3/R2 chain (3n+3 rounds)
  apply stepStar_stepPlus_stepPlus (r3r2_chain (3*n+3) 0 (n+1) 0)
  -- State: (0+(3*n+3), (n+1)+1, 0, 0, 0) = (3*n+3, n+2, 0, 0, 0)
  rw [show 0 + (3 * n + 3) = (2 * n + 1) + 1 + (n + 1) from by ring,
      show (n + 1) + 1 = 0 + 1 + (n + 1) from by ring]
  -- Phase 4: tail chain then tail end
  apply stepStar_stepPlus_stepPlus (tail_chain (n+1) (2*n+1) 0)
  -- State: (2*n+1+1+2*(n+1), 0+1, 0, 0, 0) = (4*n+4, 1, 0, 0, 0)
  rw [show 2 * n + 1 + 1 + 2 * (n + 1) = (4 * n + 3) + 1 from by ring,
      show 0 + 1 = 1 from by ring]
  exact tail_end

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 2⟩)
  · execute fm 15
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2*n+1, 0, 0, 0, 2⟩) 0
  intro n
  exact ⟨2*n+1, by
    rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_34
