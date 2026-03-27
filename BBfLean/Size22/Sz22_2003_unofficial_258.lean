import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #258: [14/15, 1/242, 507/2, 55/13, 2/77]

Vector representation:
```
 1 -1 -1  1  0  0
-1  0  0  0 -2  0
-1  1  0  0  0  2
 0  0  1  0  1 -1
 1  0  0 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_258

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+2, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+2⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- Phase 1: R5/R2 drain. (0,0,C,D+j,3j+2,0) →* (0,0,C,D,2,0)
theorem r5r2_drain : ∀ j, ∀ C D,
    ⟨0, 0, C, D+j, 3*j+2, 0⟩ [fm]⊢* ⟨0, 0, C, D, 2, 0⟩ := by
  intro j; induction' j with j ih <;> intro C D
  · exists 0
  rw [show D + (j + 1) = (D + j) + 1 from by ring,
      show 3 * (j + 1) + 2 = (3 * j + 2) + 3 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  finish

-- Phase 2: R5 then R3 from (0,0,C,D+1,2,0) → (0,1,C,D,1,2)
-- Actually: (0,0,C,D+1,2,0) →R5→ (1,0,C,D,1,0) →R3→ (0,1,C,D,1,2)
theorem r5_r3_entry : ⟨0, 0, C, D+1, 2, 0⟩ [fm]⊢* ⟨0, 1, C, D, 1, 2⟩ := by
  step fm; step fm; finish

-- Phase 3: R1/R3 loop. (0,1,j,D,1,F) →* (0,1,0,D+j,1,F+2*j)
-- Each pair: R1 → (1,0,c-1,D+1,1,F) → R3 → (0,1,c-1,D+1,1,F+2)
theorem r1r3_loop : ∀ j, ∀ D F,
    ⟨0, 1, j, D, 1, F⟩ [fm]⊢* ⟨0, 1, 0, D+j, 1, F+2*j⟩ := by
  intro j; induction' j with j ih <;> intro D F
  · exists 0
  rw [show (j + 1 : ℕ) = j + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 4: Entry to R4 loop. (0,1,0,D+1,1,F) →* (0,0,0,D+1,0,F)
-- R4: (0,1,0,D+1,1,F) → (0,1,1,D+1,2,F-1) → R1 → (1,0,0,D+2,2,F-1) → R2 → (0,0,0,D+2,0,F-1)
-- Wait, let me re-examine. At (0,1,0,D,1,F): b=1, c=0, so R1 doesn't apply.
-- a=0, so R2,R3 don't apply. f=F, so if F>=1, R4 applies.
-- R4: (0,1,1,D,2,F-1). Now b=1,c=1 so R1: (1,0,0,D+1,2,F-1). a=1,e=2 so R2: (0,0,0,D+1,0,F-1)
-- Hmm, that gives D+1 not D+2. Let me redo.
theorem phase4_entry : ⟨0, 1, 0, D, 1, F+1⟩ [fm]⊢* ⟨0, 0, 0, D+1, 0, F⟩ := by
  step fm; step fm; step fm; finish

-- Phase 5: R4 loop. (0,0,0,D,0,j) →* (0,0,j,D,j,0)
theorem r4_loop : ∀ j, ∀ C D E,
    ⟨0, 0, C, D, E, j⟩ [fm]⊢* ⟨0, 0, C+j, D, E+j, 0⟩ := by
  intro j; induction' j with j ih <;> intro C D E
  · exists 0
  rw [show (j + 1 : ℕ) = j + 1 from rfl]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Combine phase 1+2: (0,0,n,d,n,0) →* (0,1,n,d-k-1,1,2) where n=3k+2, d=2(k+1)
-- = (0,0,3k+2,2(k+1),3k+2,0) →* (0,1,3k+2,k+1,1,2)
-- Phase 1: r5r2_drain with j=k: (0,0,3k+2,(k+2)+k,3k+2,0) →* (0,0,3k+2,k+2,2,0)
-- Phase 2: r5_r3_entry: (0,0,3k+2,(k+1)+1,2,0) →* (0,1,3k+2,k+1,1,2)

-- Main transition: (0,0,3k+2,2(k+1),3k+2,0) ⊢⁺ (0,0,6k+5,4(k+1),6k+5,0)
-- = (0,0,3(2k+1)+2,2((2k+1)+1),3(2k+1)+2,0)
-- Combined all phases into a stepStar
theorem main_trans_star (k : ℕ) :
    ⟨0, 0, 3*k+2, 2*(k+1), 3*k+2, 0⟩ [fm]⊢* ⟨0, 0, 3*(2*k+1)+2, 2*((2*k+1)+1), 3*(2*k+1)+2, 0⟩ := by
  -- Phase 1: R5/R2 drain
  rw [show 2 * (k + 1) = (k + 2) + k from by ring]
  apply stepStar_trans (r5r2_drain k (3*k+2) (k+2))
  -- Phase 2: R5 then R3
  rw [show (k + 2 : ℕ) = (k + 1) + 1 from by ring]
  apply stepStar_trans (r5_r3_entry (C := 3*k+2) (D := k+1))
  -- Phase 3: R1/R3 loop
  apply stepStar_trans (r1r3_loop (3*k+2) (k+1) 2)
  -- Phase 4: Entry
  rw [show k + 1 + (3 * k + 2) = 4 * k + 3 from by ring,
      show 2 + 2 * (3 * k + 2) = (6 * k + 5) + 1 from by ring]
  apply stepStar_trans (phase4_entry (D := 4*k+3) (F := 6*k+5))
  -- Phase 5: R4 loop
  rw [show (4 * k + 3 : ℕ) + 1 = 4 * k + 4 from by ring]
  have h5 := r4_loop (6*k+5) 0 (4*k+4) 0
  simp only [Nat.zero_add] at h5
  apply stepStar_trans h5
  ring_nf; finish

theorem main_trans (k : ℕ) :
    ⟨0, 0, 3*k+2, 2*(k+1), 3*k+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*(2*k+1)+2, 2*((2*k+1)+1), 3*(2*k+1)+2, 0⟩ := by
  apply stepStar_stepPlus (main_trans_star k)
  intro h
  have h1 : (⟨0, 0, 3*k+2, 2*(k+1), 3*k+2, 0⟩ : Q).2.2.1 = (3*k+2) := rfl
  have h2 : (⟨0, 0, 3*(2*k+1)+2, 2*((2*k+1)+1), 3*(2*k+1)+2, 0⟩ : Q).2.2.1 = (3*(2*k+1)+2) := rfl
  rw [h] at h1; rw [h1] at h2; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 2, 2, 0⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 3*k+2, 2*(k+1), 3*k+2, 0⟩) 0
  intro k
  exact ⟨2*k+1, by
    show ⟨0, 0, 3*k+2, 2*(k+1), 3*k+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*(2*k+1)+2, 2*((2*k+1)+1), 3*(2*k+1)+2, 0⟩
    exact main_trans k⟩

end Sz22_2003_unofficial_258
