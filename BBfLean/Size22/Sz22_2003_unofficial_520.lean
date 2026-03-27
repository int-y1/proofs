import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #520: [28/15, 3/22, 845/2, 11/7, 33/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  2
 0  0  0 -1  1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_520

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+2⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

-- R4 repeated: transfer d to e
theorem d_to_e : ∀ k, ∀ c d e f, ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* (⟨0, 0, c, d, e+k, f⟩ : Q) := by
  intro k; induction' k with k h <;> intro c d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R1/R2 interleave: each pair transfers one unit from c,e to a,d
theorem r1r2_chain : ∀ k, ∀ a c d e f, ⟨a, 1, c+k, d, e+k, f⟩ [fm]⊢* (⟨a+k, 1, c, d+k, e, f⟩ : Q) := by
  intro k; induction' k with k h <;> intro a c d e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _ _ _)
  ring_nf; finish

-- R2 repeated: transfer from a,e to b
theorem r2_drain : ∀ k, ∀ a b d f, ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* (⟨a, b+k, 0, d, 0, f⟩ : Q) := by
  intro k; induction' k with k h <;> intro a b d f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R3/R1 interleave: each pair transfers one unit from b to a,d and adds 2 to f
theorem r3r1_chain : ∀ k, ∀ a d f, ⟨a+1, k, 0, d, 0, f⟩ [fm]⊢* (⟨a+k+1, 0, 0, d+k, 0, f+2*k⟩ : Q) := by
  intro k; induction' k with k h <;> intro a d f
  · exists 0
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: transfer a to c and add 2 to f per step
theorem r3_chain : ∀ k, ∀ c d f, ⟨k, 0, c, d, 0, f⟩ [fm]⊢* (⟨0, 0, c+k, d, 0, f+2*k⟩ : Q) := by
  intro k; induction' k with k h <;> intro c d f
  · exists 0
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 2a rest: after R5 and R1, drain the remaining interleave
-- (2, 0, n, 1, 2*n+1, f) →* (n+2, 0, 0, n+1, n+1, f)
theorem interleave_rest : ∀ n f, ⟨2, 0, n, 1, 2*n+1, f⟩ [fm]⊢* (⟨n+2, 0, 0, n+1, n+1, f⟩ : Q) := by
  intro n; induction' n with n ih <;> intro f
  · exists 0
  -- State: (2, 0, n+1, 1, 2n+3, f)
  -- R2: (1, 1, n+1, 1, 2n+2, f)
  have h1 : (⟨2, 0, n+1, 1, 2*(n+1)+1, f⟩ : Q) = ⟨1+1, 0, n+1, 1, (2*n+2)+1, f⟩ := by ring_nf
  rw [h1]; step fm
  -- State after step: (1, 1, n+1, 1, 2n+2, f)
  -- Apply r1r2_chain n
  have h2 : (⟨1, 1, n+1, 1, 2*n+2, f⟩ : Q) = ⟨1, 1, 1+n, 1, (n+2)+n, f⟩ := by ring_nf
  rw [h2]
  apply stepStar_trans (r1r2_chain n 1 1 1 (n+2) f)
  -- State: (1+n, 1, 1, 1+n, n+2, f)
  -- R1: (n+3, 0, 0, n+2, n+2, f)
  have h3 : (⟨1+n, 1, 1, 1+n, n+2, f⟩ : Q) = ⟨n+1, 1, 1, n+1, n+2, f⟩ := by ring_nf
  rw [h3]; step fm
  ring_nf; finish

-- Main transition
theorem main_trans (n f : ℕ) : ⟨0, 0, n+1, 2*n, 0, f+1⟩ [fm]⊢⁺ (⟨0, 0, n+2, 2*n+2, 0, f+4*n+6⟩ : Q) := by
  -- Phase 1: d_to_e: (0,0,n+1,2n,0,f+1) →* (0,0,n+1,0,2n,f+1)
  rw [show 2 * n = 0 + 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (2*n) (n+1) 0 0 (f+1))
  rw [show 0 + 2 * n = 2 * n from by ring]
  -- Phase 2a: R5 step (gives ⊢⁺)
  -- State: (0, 0, n+1, 0, 2n, f+1)
  -- R5: (0, 1, n+1, 0, 2n+1, f)
  step fm
  -- Now goal is ⊢* from (0, 1, n+1, 0, 2n+1, f)
  -- R1: (2, 0, n, 1, 2n+1, f)
  have h1 : (⟨0, 1, n+1, 0, 2*n+1, f⟩ : Q) = ⟨0, 0+1, n+1, 0, (2*n)+1, f⟩ := by ring_nf
  rw [h1]; step fm
  -- Apply interleave_rest
  apply stepStar_trans (interleave_rest n f)
  -- Phase 2b: R2 drain: (n+2, 0, 0, n+1, n+1, f) →* (1, n+1, 0, n+1, 0, f)
  rw [show n + 2 = 1 + (n + 1) from by ring]
  apply stepStar_trans (r2_drain (n+1) 1 0 (n+1) f)
  rw [show 0 + (n + 1) = n + 1 from by ring]
  -- Phase 2c: R3/R1 chain: (1, n+1, 0, n+1, 0, f) →* (n+2, 0, 0, 2n+2, 0, f+2*(n+1))
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1_chain (n+1) 0 (n+1) f)
  rw [show 0 + (n + 1) + 1 = n + 2 from by ring,
      show n + 1 + (n + 1) = 2 * n + 2 from by ring]
  -- Phase 3: R3 chain: (n+2, 0, 0, 2n+2, 0, f+2*(n+1)) →* (0, 0, n+2, 2n+2, 0, f+2*(n+1)+2*(n+2))
  apply stepStar_trans (r3_chain (n+2) 0 (2*n+2) (f+2*(n+1)))
  rw [show 0 + (n + 2) = n + 2 from by ring]
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨0, 0, 1, 0, 0, 2⟩ : Q))
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = (⟨0, 0, n+1, 2*n, 0, f+1⟩ : Q))
  · intro c ⟨n, f, hq⟩; subst hq
    exact ⟨⟨0, 0, n+2, 2*n+2, 0, f+4*n+6⟩,
           ⟨n+1, f+4*n+5, by ring_nf⟩,
           main_trans n f⟩
  · exact ⟨0, 1, by ring_nf⟩

end Sz22_2003_unofficial_520
