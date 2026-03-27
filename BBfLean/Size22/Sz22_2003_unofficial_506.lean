import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #506: [28/15, 3/22, 35/2, 11/7, 12/11]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  1  1  0
 0  0  0 -1  1
 2  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_506

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

-- R3 chain: (k+1, 0, c, d, 0) ->* (0, 0, c+k+1, d+k+1, 0)
theorem r3_chain : ∀ k, ∀ c d, ⟨k+1, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c+k+1, d+k+1, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · step fm; finish
  step fm
  apply stepStar_trans (ih (c + 1) (d + 1))
  ring_nf; finish

-- R4 chain: (0, 0, c, d+k+1, e) ->* (0, 0, c, d, e+k+1)
theorem r4_chain_00 : ∀ k, ∀ c d e, ⟨0, 0, c, d+k+1, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; finish
  rw [← Nat.add_assoc d]
  step fm
  apply stepStar_trans (ih c d (e + 1))
  ring_nf; finish

-- R4 chain: (0, b, 0, d+k+1, e) ->* (0, b, 0, d, e+k+1)
theorem r4_chain_b0 : ∀ k, ∀ b d e, ⟨0, b, 0, d+k+1, e⟩ [fm]⊢* ⟨0, b, 0, d, e+k+1⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · step fm; finish
  rw [← Nat.add_assoc d]
  step fm
  apply stepStar_trans (ih b d (e + 1))
  ring_nf; finish

-- R2,R1 interleaved chain
theorem r2r1_chain : ∀ k, ∀ a d e, ⟨a+1, 0, k+1, d, e+k+1⟩ [fm]⊢* ⟨a+k+2, 0, 0, d+k+1, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · step fm; step fm; finish
  rw [← Nat.add_assoc e]
  step fm; step fm
  apply stepStar_trans (ih (a + 1) (d + 1) e)
  ring_nf; finish

-- R5 + R1 + (R2,R1)^k: (0, 0, k+2, 0, e+k+2) ->* (k+5, 0, 0, k+2, e)
theorem phase3 : ⟨0, 0, k+2, 0, e+k+2⟩ [fm]⊢* ⟨k+5, 0, 0, k+2, e⟩ := by
  rw [show e + k + 2 = (e + k) + 1 + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (r2r1_chain k 3 1 e)
  ring_nf; finish

-- R2 chain: (a+k+1, b, 0, d, e+k+1) ->* (a, b+k+1, 0, d, e)
theorem r2_chain : ∀ k, ∀ a b d e, ⟨a+k+1, b, 0, d, e+k+1⟩ [fm]⊢* ⟨a, b+k+1, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · step fm; finish
  rw [← Nat.add_assoc a, ← Nat.add_assoc e]
  step fm
  apply stepStar_trans (ih a (b + 1) d e)
  ring_nf; finish

-- R5,R2,R2 chain: (0, b, 0, 0, 3k+4) ->* (0, b+3k+3, 0, 0, 1)
theorem r5r2r2_chain : ∀ k, ∀ b, ⟨0, b, 0, 0, 3*k+4⟩ [fm]⊢* ⟨0, b+3*k+3, 0, 0, 1⟩ := by
  intro k; induction' k with k ih <;> intro b
  · step fm; step fm; step fm; finish
  rw [show 3 * (k + 1) + 4 = (3 * k + 4) + 3 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (b + 3))
  ring_nf; finish

-- R3,R1 chain: (a+1, b+k+1, 0, d, 0) ->* (a+k+2, b, 0, d+2k+2, 0)
theorem r3r1_chain : ∀ k, ∀ a b d, ⟨a+1, b+k+1, 0, d, 0⟩ [fm]⊢* ⟨a+k+2, b, 0, d+2*k+2, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · step fm; step fm; finish
  rw [← Nat.add_assoc b]
  step fm; step fm
  apply stepStar_trans (ih (a + 1) b (d + 2))
  ring_nf; finish

-- Full transition: (3m+7, 0, 0, 6m+10, 0) ⊢⁺ (9m+19, 0, 0, 18m+34, 0)
theorem main_trans (m : ℕ) :
    ⟨3*m+7, 0, 0, 6*m+10, 0⟩ [fm]⊢⁺ ⟨9*m+19, 0, 0, 18*m+34, 0⟩ := by
  -- Phase 1: R3 chain -> (0, 0, 3m+7, 9m+17, 0)
  have h1 := r3_chain (3*m+6) 0 (6*m+10)
  rw [show (3*m+6)+1 = 3*m+7 from by ring,
      show 0+(3*m+6)+1 = 3*m+7 from by ring,
      show 6*m+10+(3*m+6)+1 = 9*m+17 from by ring] at h1
  -- Phase 2: R4 chain -> (0, 0, 3m+7, 0, 9m+17)
  have h2 := r4_chain_00 (9*m+16) (3*m+7) 0 0
  rw [show 0+(9*m+16)+1 = 9*m+17 from by ring] at h2
  -- Phase 3: -> (3m+10, 0, 0, 3m+7, 6m+10)
  have h3 := @phase3 (3*m+5) (6*m+10)
  rw [show (3*m+5)+2 = 3*m+7 from by ring,
      show 6*m+10+(3*m+5)+2 = 9*m+17 from by ring,
      show (3*m+5)+5 = 3*m+10 from by ring,
      show (3*m+5)+2 = 3*m+7 from by ring] at h3
  -- Phase 4: R2 chain -> (0, 3m+10, 0, 3m+7, 3m)
  have h4 := r2_chain (3*m+9) 0 0 (3*m+7) (3*m)
  rw [show 0+(3*m+9)+1 = 3*m+10 from by ring,
      show 3*m+(3*m+9)+1 = 6*m+10 from by ring] at h4
  -- Phase 5: R4 chain -> (0, 3m+10, 0, 0, 6m+7)
  have h5 := r4_chain_b0 (3*m+6) (3*m+10) 0 (3*m)
  rw [show 0+(3*m+6)+1 = 3*m+7 from by ring,
      show 3*m+(3*m+6)+1 = 6*m+7 from by ring] at h5
  -- Phase 6: first R5R2R2 round + chain -> (0, 9m+16, 0, 0, 1)
  have h6a : ⟨0, 3*m+10, 0, 0, 6*m+7⟩ [fm]⊢* ⟨0, 3*m+13, 0, 0, 6*m+4⟩ := by
    rw [show 6*m+7 = (6*m+4)+3 from by ring]
    step fm; step fm; step fm; finish
  have h6b := r5r2r2_chain (2*m) (3*m+13)
  rw [show 3*(2*m)+4 = 6*m+4 from by ring,
      show 3*m+13+3*(2*m)+3 = 9*m+16 from by ring] at h6b
  -- Phase 7: R5 -> (2, 9m+17, 0, 0, 0)
  have h7 : ⟨0, 9*m+16, 0, 0, 1⟩ [fm]⊢* ⟨2, 9*m+17, 0, 0, 0⟩ := by
    step fm; finish
  -- Phase 8: R3 then R3R1 chain -> (9m+19, 0, 0, 18m+34, 0)
  have h8a : ⟨2, 9*m+17, 0, 0, 0⟩ [fm]⊢* ⟨1, 9*m+17, 1, 1, 0⟩ := by
    step fm; finish
  have h8b : ⟨1, 9*m+17, 1, 1, 0⟩ [fm]⊢⁺ ⟨3, 9*m+16, 0, 2, 0⟩ := by
    step fm; finish
  have h8c := r3r1_chain (9*m+15) 2 0 2
  rw [show 0+(9*m+15)+1 = 9*m+16 from by ring,
      show 2+(9*m+15)+2 = 9*m+19 from by ring,
      show 2+2*(9*m+15)+2 = 18*m+34 from by ring] at h8c
  -- Compose all phases
  apply stepStar_stepPlus_stepPlus h1
  apply stepStar_stepPlus_stepPlus h2
  apply stepStar_stepPlus_stepPlus h3
  apply stepStar_stepPlus_stepPlus h4
  apply stepStar_stepPlus_stepPlus h5
  apply stepStar_stepPlus_stepPlus h6a
  apply stepStar_stepPlus_stepPlus h6b
  apply stepStar_stepPlus_stepPlus h7
  apply stepStar_stepPlus_stepPlus h8a
  apply stepPlus_stepStar_stepPlus h8b
  exact h8c

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 6, 0⟩) (by execute fm 24)
  apply stepStar_not_halts_not_halts (c₂ := ⟨10, 0, 0, 19, 0⟩) (by execute fm 52)
  apply stepStar_not_halts_not_halts (c₂ := ⟨31, 0, 0, 58, 0⟩) (by execute fm 156)
  show ¬halts fm ⟨3*8+7, 0, 0, 6*8+10, 0⟩
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun m ↦ ⟨3*m+7, 0, 0, 6*m+10, 0⟩) 8
  intro m
  refine ⟨3*m+4, ?_⟩
  convert main_trans m using 2; ring_nf
