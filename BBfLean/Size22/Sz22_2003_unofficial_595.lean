import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #595: [35/6, 121/2, 4/55, 3/7, 105/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 0  1  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_595

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k, ∀ b, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b+k, 0, 0, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R3,R2,R2 drain: each round converts 1 unit of c into 3 units of e
theorem drain : ∀ k, ∀ c e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+1+3*k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  -- After R3,R2,R2: (0, 0, c+k, d, e+4)
  -- Need to show: (0, 0, c+k, d, e+4) ⊢* (0, 0, c, d, e+1+3*(k+1))
  -- e+4 = (e+3)+1, and e+1+3*(k+1) = (e+3)+1+3*k
  rw [show e + 4 = (e + 3) + 1 from by ring]
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1,R1,R3 chain: interleave rounds
theorem r1r1r3_chain :
    ∀ k, ∀ c d e, ⟨2, 2*k+1, c, d, e+k⟩ [fm]⊢* ⟨2, 1, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: C(n) →⁺ C(n+1)
-- C(n) = (0, 0, 0, 2*(n+1), n*n+4*n+5)
theorem main_trans :
    ⟨0, 0, 0, 2*(n+1), n*n+4*n+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*(n+2), n*n+6*n+10⟩ := by
  rw [show n*n+4*n+5 = (n*n+3*n+2) + (n+1) + 2 from by ring]
  -- Phase 1: first R4 step (gives ⊢⁺)
  rw [show 2*(n+1) = (2*n+1) + 1 from by ring]
  step fm
  -- Phase 1b: remaining R4 steps
  apply stepStar_trans (d_to_b (2*n+1) 1)
  rw [show 1 + (2*n+1) = 2*(n+1) from by ring]
  -- Phase 2: R5, R3
  step fm; step fm
  -- Phase 3: R1R1R3 chain
  apply stepStar_trans (r1r1r3_chain (n+1) 0 1 (n*n+3*n+2))
  -- Phase 4: R1,R2 ending
  step fm; step fm
  -- Phase 5: Drain
  rw [show n*n+3*n+2+2 = (n*n+3*n+3) + 1 from by ring,
      show 0 + (n+1) + 1 = 0 + (n+2) from by ring]
  apply stepStar_trans (drain (n+2) 0 (n*n+3*n+3) (d := 1+2*(n+1)+1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2*(n+1), n*n+4*n+5⟩) 0
  intro n; exists n+1
  have h := @main_trans n
  convert h using 2; ring_nf

end Sz22_2003_unofficial_595
