import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #48: [1/15, 7/3, 18/77, 25/49, 363/2]

Vector representation:
```
 0 -1 -1  0  0
 0 -1  0  1  0
 1  2  0 -1 -1
 0  0  2 -2  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_48

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3,R2,R2 chain: each 3-step round transfers one from e to a and d
theorem r3r2r2_chain : ∀ k, ∀ a d e,
    ⟨a, 0, 0, d+1, e+k⟩ [fm]⊢* ⟨a+k, 0, 0, d+1+k, e⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring,
      show d + 1 + (k + 1) = (d + 1 + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 chain: each step transfers 2 from d to c
theorem r4_chain : ∀ k, ∀ a c d,
    ⟨a, 0, c, d + 2*k, 0⟩ [fm]⊢* ⟨a, 0, c + 2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5,R1 drain: (a+k, 0, k, 0, e) -> (a, 0, 0, 0, e+2k)
theorem r5r1_drain : ∀ k, ∀ a e,
    ⟨a + k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + 2*k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2) + 2 * k from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Phase D: 5 fixed steps from (N+3, 0, N+3, 1, 0) to (N+3, 0, N, 0, 1)
theorem phaseD : ∀ N, ⟨N+3, 0, N+3, 1, 0⟩ [fm]⊢* ⟨N+3, 0, N, 0, 1⟩ := by
  intro N; step fm; step fm; step fm; step fm; step fm; finish

-- Opening 2 steps: (A+1, 0, 0, 0, E) -> (A, 0, 0, 1, E+2)
theorem opening (A E : ℕ) : ⟨A+1, 0, 0, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 1, E+2⟩ := by
  execute fm 2

-- Combined first half: (1,0,0,0,2K+4) ⊢⁺ (3,0,0,0,4K+7)
-- Steps: R5 -> (0,1,0,0,2K+6) -> R2 -> (0,0,0,1,2K+6) [opening with A=0, E=2K+4]
--        -> R3R2R2 chain (2K+6 rounds) -> (2K+6, 0, 0, 2K+7, 0)
--        -> R4 chain (K+3 rounds) -> (2K+6, 0, 2K+6, 1, 0)
--        -> phaseD (N=2K+3) -> (2K+6, 0, 2K+3, 0, 1)
--        -> R5R1 drain (k=2K+3, a=3) -> (3, 0, 0, 0, 4K+7)
theorem firstHalf (K : ℕ) :
    ⟨1, 0, 0, 0, 2*K+4⟩ [fm]⊢⁺ ⟨3, 0, 0, 0, 4*K+7⟩ := by
  -- Opening: 2 steps give ⊢⁺
  apply step_stepStar_stepPlus
  · show fm ⟨1, 0, 0, 0, 2*K+4⟩ = some ⟨0, 1, 0, 0, 2*K+6⟩; rfl
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 1, 2*K+6⟩)
  · show ⟨0, 1, 0, 0, 2*K+6⟩ [fm]⊢* ⟨0, 0, 0, 1, 2*K+6⟩; execute fm 1
  apply stepStar_trans (c₂ := ⟨2*K+6, 0, 0, 2*K+7, 0⟩)
  · have h := r3r2r2_chain (2*K+6) 0 0 0
    rw [show (0 : ℕ) + 1 = 1 from by ring,
        show (0 : ℕ) + (2 * K + 6) = 2 * K + 6 from by ring,
        show 0 + 1 + (2 * K + 6) = 2 * K + 7 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨2*K+6, 0, 2*K+6, 1, 0⟩)
  · have h := r4_chain (K+3) (2*K+6) 0 1
    rw [show 1 + 2 * (K + 3) = 2 * K + 7 from by ring,
        show (0 : ℕ) + 2 * (K + 3) = 2 * K + 6 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨2*K+6, 0, 2*K+3, 0, 1⟩)
  · have h := phaseD (2*K+3)
    rw [show 2 * K + 3 + 3 = 2 * K + 6 from by ring] at h; exact h
  have h := r5r1_drain (2*K+3) 3 1
  rw [show 3 + (2 * K + 3) = 2 * K + 6 from by ring,
      show 1 + 2 * (2 * K + 3) = 4 * K + 7 from by ring] at h; exact h

-- Second half: (3,0,0,0,4K+7) ⊢⁺ (1,0,0,0,8K+20)
theorem secondHalf (K : ℕ) :
    ⟨3, 0, 0, 0, 4*K+7⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 8*K+20⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨3, 0, 0, 0, 4*K+7⟩ = some ⟨2, 1, 0, 0, 4*K+9⟩; rfl
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 1, 4*K+9⟩)
  · show ⟨2, 1, 0, 0, 4*K+9⟩ [fm]⊢* ⟨2, 0, 0, 1, 4*K+9⟩; execute fm 1
  apply stepStar_trans (c₂ := ⟨4*K+11, 0, 0, 4*K+10, 0⟩)
  · have h := r3r2r2_chain (4*K+9) 2 0 0
    rw [show (0 : ℕ) + 1 = 1 from by ring,
        show (0 : ℕ) + (4 * K + 9) = 4 * K + 9 from by ring,
        show 0 + 1 + (4 * K + 9) = 4 * K + 10 from by ring,
        show 2 + (4 * K + 9) = 4 * K + 11 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨4*K+11, 0, 4*K+10, 0, 0⟩)
  · have h := r4_chain (2*K+5) (4*K+11) 0 0
    rw [show (0 : ℕ) + 2 * (2 * K + 5) = 4 * K + 10 from by ring] at h; exact h
  have h := r5r1_drain (4*K+10) 1 0
  rw [show 1 + (4 * K + 10) = 4 * K + 11 from by ring,
      show 0 + 2 * (4 * K + 10) = 8 * K + 20 from by ring] at h; exact h

-- Full transition
theorem fullTrans (K : ℕ) :
    ⟨1, 0, 0, 0, 2*K+4⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2*(4*K+8)+4⟩ := by
  apply stepPlus_trans (firstHalf K)
  rw [show 2 * (4 * K + 8) + 4 = 8 * K + 20 from by ring]
  exact secondHalf K

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 2*0+4⟩) (by execute fm 22)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun K ↦ ⟨1, 0, 0, 0, 2*K+4⟩) 0
  intro K; exact ⟨4*K+8, fullTrans K⟩

end Sz22_2003_unofficial_48
