import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1164: [5/6, 44/35, 91/2, 3/11, 55/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  1
 0  1  0  0 -1  0
 0  0  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1164

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | _ => none

-- R3 chain: drain a into d and f (b=0, c=0).
theorem r3_chain : ∀ k d f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d f
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1) (f + 1))
    ring_nf; finish

-- R4 chain: drain e into b (a=0, c=0).
theorem r4_chain : ∀ k b e, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- R2R1R1 chain: interleaved drain.
theorem r2r1r1_chain : ∀ k c d e, ⟨0, 2 * k, c + 1, d + k, e, f⟩ [fm]⊢* ⟨0, 0, c + k + 1, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- R3R2 chain: alternating R3 and R2.
theorem r3r2_chain : ∀ k a e f, ⟨a + 1, 0, c + k, 0, e, f⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    apply stepStar_trans (ih (a + 1) (e + 1) (f + 1))
    ring_nf; finish

-- Main transition as stepPlus: C(n) →⁺ C(n+1)
-- C(n) = (n+2, 0, 0, 0, 2n+2, n²+n)
theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, 0, 2 * n + 2, n * n + n⟩ [fm]⊢⁺
    ⟨n + 3, 0, 0, 0, 2 * n + 4, n * n + 3 * n + 2⟩ := by
  -- Phase 1: First R3 step (for stepPlus)
  rw [show n + 2 = n + 1 + 1 from by ring]
  step fm
  -- After first R3: (n+1, 0, 0, 1, 2n+2, n*n+n+1)
  -- Remaining R3 steps (n+1 more)
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r3_chain (n + 1) 1 (n * n + n + 1) (a := 0) (e := 2 * n + 2))
  -- (0, 0, 0, 1+(n+1), 2n+2, n*n+n+1+(n+1))
  rw [show n * n + n + 1 + (n + 1) = n * n + 2 * n + 2 from by ring,
      show 1 + (n + 1) = n + 2 from by ring]
  -- Phase 2: R4 chain (2n+2 steps)
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r4_chain (2 * n + 2) 0 0 (d := n + 2) (f := n * n + 2 * n + 2))
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring]
  -- (0, 2n+2, 0, n+2, 0, n²+2n+2)
  -- Phase 3: R5 step
  rw [show n * n + 2 * n + 2 = n * n + 2 * n + 1 + 1 from by ring]
  step fm
  -- (0, 2n+2, 1, n+2, 1, n²+2n+1)
  -- Phase 4: R2R1R1 chain (n+1 rounds)
  rw [show 2 * n + 2 = 2 * (n + 1) from by ring,
      show n + 2 = 1 + (n + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (n + 1) 0 1 1 (f := n * n + 2 * n + 1))
  -- (0, 0, 0+(n+1)+1, 1, 1+(n+1), n²+2n+1)
  rw [show 0 + (n + 1) + 1 = n + 1 + 1 from by ring,
      show 1 + (n + 1) = n + 1 + 1 from by ring]
  -- Phase 5: R2 step
  step fm
  -- (2, 0, n+1, 0, n+1+1+1, n²+2n+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show n + 1 + 1 + 1 = n + 3 from by ring,
      show n + 1 = 0 + (n + 1) from by ring]
  -- Phase 6: R3R2 chain (n+1 rounds)
  apply stepStar_trans (r3r2_chain (n + 1) 1 (n + 3) (n * n + 2 * n + 1) (c := 0))
  rw [show 1 + (n + 1) + 1 = n + 3 from by ring,
      show n + 3 + (n + 1) = 2 * n + 4 from by ring,
      show n * n + 2 * n + 1 + (n + 1) = n * n + 3 * n + 2 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2, n * n + n⟩) 0
  intro n; exists n + 1
  show ⟨n + 2, 0, 0, 0, 2 * n + 2, n * n + n⟩ [fm]⊢⁺ ⟨n + 1 + 2, 0, 0, 0, 2 * (n + 1) + 2, (n + 1) * (n + 1) + (n + 1)⟩
  rw [show n + 1 + 2 = n + 3 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring,
      show (n + 1) * (n + 1) + (n + 1) = n * n + 3 * n + 2 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1164
