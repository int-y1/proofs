import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #547: [28/45, 33/2, 1/231, 75/11, 1/3]

Vector representation:
```
 2 -2 -1  1  0
-1  1  0  0  1
 0 -1  0 -1 -1
 0  1  2  0 -1
 0 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_547

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- R2,R2,R1 chain: each round consumes 1 c, adds 1 d, adds 2 e
theorem r2r2r1_chain : ∀ k c d e, ⟨2, 0, c+k, d, e⟩ [fm]⊢* ⟨2, 0, c, d+k, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4,R3 chain: each round adds 2 c, removes 1 d, removes 2 e
theorem r4r3_chain : ∀ k c d e, ⟨0, 0, c, d+k, e+2*k⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by omega,
      show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by omega]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2,R2,R3,R3: preserves e, removes 2 from d
theorem r2r2r3r3 : ⟨2, 0, 0, d+2, e+1⟩ [fm]⊢* ⟨0, 0, 0, d, e+1⟩ := by
  step fm; step fm; step fm; step fm; finish

-- R4,R4,R1 finish
theorem r4r4r1 : ⟨0, 0, c+1, 0, 2⟩ [fm]⊢⁺ ⟨2, 0, c+4, 1, 0⟩ := by
  step fm; step fm; step fm; finish

-- Main transition for D≥1: (0, 0, 0, D+1, 2*(D+1)+2) →⁺ (0, 0, 0, 2*(D+1)+2, 2*(2*(D+1)+2)+2)
-- i.e. (0, 0, 0, D+1, 2*D+4) →⁺ (0, 0, 0, 2*D+4, 4*D+10)
theorem main_trans_pos : ⟨0, 0, 0, D+1, 2*D+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*D+4, 4*D+10⟩ := by
  -- Phase 1: R4R3 chain (D+1) times
  rw [show (D+1 : ℕ) = 0+(D+1) from by omega,
      show (2*D+4 : ℕ) = 2 + 2*(D+1) from by omega]
  apply stepStar_stepPlus_stepPlus (r4r3_chain (D+1) 0 0 2)
  simp only [Nat.zero_add]
  -- Now at (0, 0, 2*(D+1), 0, 2)
  -- Phase 2: R4,R4,R1
  rw [show 2*(D+1) = (2*D+1)+1 from by omega]
  apply stepPlus_stepStar_stepPlus r4r4r1
  -- Now at (2, 0, 2*D+5, 1, 0)
  rw [show (2*D+5 : ℕ) = 0 + (2*D+5) from by omega]
  -- Phase 3: R2R2R1 chain (2*D+5) times
  apply stepStar_trans (r2r2r1_chain (2*D+5) 0 1 0)
  simp only [Nat.zero_add]
  -- Goal has: (2, 0, 0, 1+(2*D+5), 2*(2*D+5)) ⊢* (0, 0, 0, ..., 4*D+10)
  -- Need to normalize and apply R2R2R3R3
  rw [show 1 + (2*D+5) = (2*D+4) + 2 from by omega,
      show 2*(2*D+5) = (4*D+9) + 1 from by omega,
      show 2 + (2*D+1+1) = 2*D+4 from by omega]
  apply stepStar_trans r2r2r3r3
  ring_nf; finish

-- Main transition for D=0: (0, 0, 0, 0, 2) →⁺ (0, 0, 0, 2, 6)
theorem main_trans_zero : ⟨0, 0, 0, 0, 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, 6⟩ := by
  -- R4,R4,R1: (0,0,0,0,2) → (2,0,3,1,0)
  step fm; step fm; step fm
  -- R2R2R1 chain 3 times: (2,0,3,1,0) → (2,0,0,4,6)
  rw [show (3 : ℕ) = 0 + 3 from by omega]
  apply stepStar_trans (r2r2r1_chain 3 0 1 0)
  -- Normalize: (2, 0, 0, 1+3, 2*3) = (2, 0, 0, 4, 6)
  norm_num
  -- R2R2R3R3: (2,0,0,4,6) → (0,0,0,2,6)
  rw [show (4 : ℕ) = 2 + 2 from by omega, show (6 : ℕ) = 5 + 1 from by omega]
  apply stepStar_trans r2r2r3r3
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D, q = ⟨0, 0, 0, D, 2*D+2⟩)
  · intro c ⟨D, hq⟩; subst hq
    rcases D with _ | D
    · exact ⟨⟨0, 0, 0, 2, 6⟩, ⟨2, by ring_nf⟩, main_trans_zero⟩
    · exact ⟨⟨0, 0, 0, 2*D+4, 4*D+10⟩, ⟨2*D+4, by ring_nf⟩, main_trans_pos⟩
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_547
