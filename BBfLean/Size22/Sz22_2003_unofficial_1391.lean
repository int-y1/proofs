import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1391: [63/10, 847/2, 4/33, 5/7, 3/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  1  2
 2 -1  0  0 -1
 0  0  1 -1  0
 0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1391

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 drain: transfer d to c
theorem d_to_c : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e); ring_nf; finish

-- R1,R1,R3 chain: each round consumes 2 from c, adds 2 to d, subtracts 1 from e, adds 3 to b
theorem r1r1r3_chain : ∀ k, ∀ b c d e, ⟨2, b, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 3 * k, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = (d + 2) from by ring]
    apply stepStar_trans (ih (b + 3) c (d + 2) e); ring_nf; finish

-- R2,R2,R3 chain: each round subtracts 1 from b, adds 2 to d, adds 3 to e
theorem r2r2r3_chain : ∀ k, ∀ b d e, ⟨2, b + k, 0, d, e⟩ [fm]⊢* ⟨2, b, 0, d + 2 * k, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans (ih b (d + 2) (e + 3)); ring_nf; finish

-- Main transition: from canonical (0,0,0,2m+2,e+m+3) to next canonical
-- After transition: d'=4(2m+2)+2=8m+10, e'=(e+m+3)+4(2m+2)+2=e+9m+13
-- Next params: m'=4m+4, e'_param=e+4m+6 so that e'+m'+3 = e+9m+13
theorem main_trans (m e : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, e + m + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 8 * m + 10, e + 9 * m + 13⟩ := by
  -- Phase 1: R4 drain: first step starts the ⊢⁺
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  -- Now at (0, 0, 1, 2m+1, e+m+3) with goal ⊢*
  -- Continue R4 drain
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_trans (d_to_c (2 * m + 1) 1 0 (e + m + 3))
  rw [show 1 + (2 * m + 1) = 2 * m + 2 from by ring]
  -- Now at (0, 0, 2m+2, 0, e+m+3)
  -- Phase 2: R5, R3
  rw [show e + m + 3 = (e + m + 1) + 1 + 1 from by ring]
  step fm; step fm
  -- Now at (2, 0, 2m+2, 0, e+m+1)
  -- Phase 3: R1,R1,R3 chain with k=m+1 rounds
  rw [show 2 * m + 2 = 0 + 2 * (m + 1) from by ring,
      show e + m + 1 = e + (m + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (m + 1) 0 0 0 e)
  rw [show 0 + 3 * (m + 1) = 0 + (3 * m + 3) from by ring,
      show 0 + 2 * (m + 1) = 2 * m + 2 from by ring]
  -- Now at (2, 3m+3, 0, 2m+2, e)
  -- Phase 4: R2,R2,R3 chain with k=3m+3 rounds
  apply stepStar_trans (r2r2r3_chain (3 * m + 3) 0 (2 * m + 2) e)
  rw [show 2 * m + 2 + 2 * (3 * m + 3) = 8 * m + 8 from by ring,
      show e + 3 * (3 * m + 3) = e + 9 * m + 9 from by ring]
  -- Now at (2, 0, 0, 8m+8, e+9m+9)
  -- Phase 5: R2, R2
  step fm; step fm
  rw [show 8 * m + 8 + 1 + 1 = 8 * m + 10 from by ring,
      show e + 9 * m + 9 + 2 + 2 = e + 9 * m + 13 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 6, 8⟩)
  · execute fm 12
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 0, 2 * p.1 + 2, p.2 + p.1 + 3⟩) ⟨2, 3⟩
  intro ⟨m, e⟩
  refine ⟨⟨4 * m + 4, e + 5 * m + 6⟩, ?_⟩
  dsimp only []
  rw [show 2 * (4 * m + 4) + 2 = 8 * m + 10 from by ring,
      show e + 5 * m + 6 + (4 * m + 4) + 3 = e + 9 * m + 13 from by ring]
  exact main_trans m e

end Sz22_2003_unofficial_1391
