import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #92: [1/30, 2/77, 147/2, 25/7, 242/5]

Vector representation:
```
-1 -1 -1  0  0
 1  0  0 -1 -1
-1  1  0  2  0
 0  0  2 -1  0
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_92

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R2 with c=0: (a, b, 0, d+1, e+1) -> (a+1, b, 0, d, e)
theorem r2_step_c0 (a b d e : ℕ) : fm ⟨a, b, 0, d+1, e+1⟩ = some ⟨a+1, b, 0, d, e⟩ := by simp [fm]

-- R2 chain with c=0: (a, b, 0, d+k, e+k) ->* (a+k, b, 0, d, e)
theorem r2_chain_c0 : ∀ k a b d e, ⟨a, b, 0, d+k, e+k⟩ [fm]⊢* ⟨a+k, b, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  exact stepStar_trans (step_stepStar (r2_step_c0 a b (d+k) (e+k)))
    (by have := ih (a+1) b d e; rw [show a + 1 + k = a + (k + 1) from by ring] at this; exact this)

-- R3 chain: (a+k, b, 0, d, 0) ->* (a, b+k, 0, d+2*k, 0)
theorem r3_chain : ∀ k a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+k, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 chain: (0, b, c, d+k, 0) ->* (0, b, c+2*k, d, 0)
theorem r4_chain : ∀ k b c d, ⟨0, b, c, d+k, 0⟩ [fm]⊢* ⟨0, b, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro b c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5+R1 chain: (0, b+k, c+2*k, 0, e) ->* (0, b, c, 0, e+2*k)
-- Note: c >= 1 needed for R5. Actually R5 pattern is c+1, so c+2*k with k>=1 works.
-- And R1 pattern needs a>=1, b>=1, c>=1. After R5 we get (1, b+k, c+2*k-1, 0, e+2).
-- R1 fires if b+k>=1 (yes since k>=1 or b>=1... but we need b+k>=1 and c+2*k-1>=1).
-- Let's be more careful: after R5 on (0, b+k, (c+2*k-1)+1, 0, e):
--   -> (1, b+k, c+2*k-1, 0, e+2)
-- For R1: need a=1>=1, b+k>=1, c+2*k-1>=1.
-- b+k >= 1 when k >= 1 (since b is Nat). c+2*k-1>=1 when c+2*k>=2, i.e., k>=1.
-- After R1: (0, b+k-1, c+2*k-2, 0, e+2) = (0, b+(k-1), c+2*(k-1), 0, e+2)
theorem r5r1_chain : ∀ k b c e, ⟨0, b+k, c+2*k, 0, e⟩ [fm]⊢* ⟨0, b, c, 0, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro b c e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring]
  step fm  -- R5: (1, (b+k)+1, c+2*k+1, 0, e+2)
  rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
  step fm  -- R1: (0, b+k, c+2*k, 0, e+2)
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 + R2x2 chain: (a+1, b, 0, 0, 2*k) ->* (a+k+1, b+k, 0, 0, 0)
theorem r3r2r2_chain : ∀ k a b, ⟨a+1, b, 0, 0, 2*k⟩ [fm]⊢* ⟨a+k+1, b+k, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm  -- R3: (a, b+1, 0, 2, 2*k+2)
  apply stepStar_trans
  · have := r2_chain_c0 2 a (b+1) 0 (2*k)
    rw [show 0 + 2 = 2 from by ring, show 2 * k + 2 = 2 * k + 2 from rfl,
        show a + 2 = a + 2 from rfl] at this; exact this
  have := h (a+1) (b+1)
  rw [show a + 1 + 1 = a + 2 from by ring,
      show a + 1 + k + 1 = a + (k + 1) + 1 from by ring,
      show b + 1 + k = b + (k + 1) from by ring] at this
  exact this

-- Main transition: (1, 0, 0, 0, 2*n) ⊢⁺ (1, 0, 0, 0, 4*n+2)
theorem main_trans (n : ℕ) : ⟨1, 0, 0, 0, 2*n⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 4*n+2⟩ := by
  -- Phase 1: (1, 0, 0, 0, 2n) ->* (n+1, n, 0, 0, 0)
  apply stepStar_stepPlus_stepPlus
  · have := r3r2r2_chain n 0 0
    rw [show 0 + 1 = 1 from by ring, show 0 + n + 1 = n + 1 from by ring,
        show 0 + n = n from by ring] at this; exact this
  -- Phase 2: (n+1, n, 0, 0, 0) ->* (0, 2n+1, 0, 2n+2, 0)
  apply stepStar_stepPlus_stepPlus
  · have := r3_chain (n+1) 0 n 0
    rw [show 0 + (n + 1) = n + 1 from by ring, show n + (n + 1) = 2*n+1 from by ring,
        show 0 + 2 * (n + 1) = 2*n+2 from by ring] at this; exact this
  -- Phase 3: (0, 2n+1, 0, 2n+2, 0) ->* (0, 2n+1, 4n+4, 0, 0)
  apply stepStar_stepPlus_stepPlus
  · have := r4_chain (2*n+2) (2*n+1) 0 0
    rw [show 0 + (2*n+2) = 2*n+2 from by ring,
        show 0 + 2*(2*n+2) = 4*n+4 from by ring] at this; exact this
  -- Phase 4: (0, 2n+1, 4n+4, 0, 0) ->* (0, 0, 2, 0, 4n+2)
  apply stepStar_stepPlus_stepPlus
  · have := r5r1_chain (2*n+1) 0 2 0
    rw [show 0 + (2*n+1) = 2*n+1 from by ring,
        show 2 + 2*(2*n+1) = 4*n+4 from by ring,
        show 0 + 2*(2*n+1) = 4*n+2 from by ring] at this; exact this
  -- Phase 5: (0, 0, 2, 0, 4n+2) -> (1, 0, 0, 0, 4n+2) in 5 steps
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm  -- R5: (1, 0, 1, 0, 4n+4)
  rw [show 4 * n + 2 + 2 = 4 * n + 4 from by ring]
  step fm  -- R3: (0, 1, 1, 2, 4n+4)
  rw [show (2 : ℕ) = 1 + 1 from by ring, show 4 * n + 4 = (4 * n + 3) + 1 from by ring]
  step fm  -- R2: (1, 1, 1, 1, 4n+3)
  step fm  -- R1: (0, 0, 0, 1, 4n+3)
  rw [show 4 * n + 3 = (4 * n + 2) + 1 from by ring]
  step fm  -- R2: (1, 0, 0, 0, 4n+2)
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by execute fm 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨1, 0, 0, 0, 2*n⟩) 0
  intro n; exists 2*n+1
  rw [show 2 * (2 * n + 1) = 4 * n + 2 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_92
