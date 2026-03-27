import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #193: [1/6, 22/35, 845/2, 21/13, 4/33]

Vector representation:
```
-1 -1  0  0  0  0
 1  0 -1 -1  1  0
-1  0  1  0  0  2
 0  1  0  1  0 -1
 2 -1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_193

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+2⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | _ => none

-- Transfer f to (b, d): (0,B,0,D,e,F+k) →* (0,B+k,0,D+k,e,F)
theorem f_to_bd : ∀ k B D e F, ⟨0, B, 0, D, e, F+k⟩ [fm]⊢* ⟨(0 : ℕ), B+k, 0, D+k, e, F⟩ := by
  intro k; induction k with
  | zero => intro B D e F; exists 0
  | succ k ih =>
    intro B D e F
    rw [show F + (k + 1) = (F + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- R5/R1/R1 loop: (0,3k+1,0,d,e+k+1,0) →* (2,0,0,d,e,0)
theorem r5r1r1_loop : ∀ k d e, ⟨0, 3*k+1, 0, d, e+k+1, 0⟩ [fm]⊢* ⟨(2 : ℕ), 0, 0, d, e, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro d e
    rw [show e + 0 + 1 = e + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show e + 1 = e + 1 from by ring]
    step fm; finish
  | succ k ih =>
    intro d e
    rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 1 + 1 + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    -- R5
    step fm
    -- R1
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 3 * k + 1 + 1 + 1 = (3 * k + 1 + 1) + 1 from by ring]
    step fm
    -- R1
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 3 * k + 1 + 1 = (3 * k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R3/R2 loop: (2,0,0,d+k,e,f) →* (2,0,0,d,e+k,f+2*k)
theorem r3r2_loop : ∀ k d e f, ⟨2, 0, 0, d+k, e, f⟩ [fm]⊢* ⟨(2 : ℕ), 0, 0, d, e+k, f+2*k⟩ := by
  intro k; induction k with
  | zero => intro d e f; exists 0
  | succ k ih =>
    intro d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    -- R3: a=2=1+1
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    -- R2: c=1=0+1, d+k+1 already has +1
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (d + k) + 1 = d + k + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 1: consume c=2 via interleaved R4/R2/R1 steps
-- (0,0,2,0,e,f+2) →* (0,0,0,0,e+2,f)
theorem phase1 : ∀ e f, ⟨0, 0, 2, 0, e, f+2⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, 0, e+2, f⟩ := by
  intro e f
  -- (0,0,2,0,e,f+2): R4 (f+2 = (f+1)+1)
  rw [show f + 2 = (f + 1) + 1 from by ring,
      show (2 : ℕ) = (1 : ℕ) + 1 from by ring]
  step fm
  -- (0,1,2,1,e,f+1): R2 (c=2=1+1, d=1=0+1)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- (1,1,1,0,e+1,f+1): R1 (a=1=0+1, b=1=0+1)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- (0,0,1,0,e+1,f+1): R4 (f+1 = f+1)
  rw [show f + 1 = f + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- (0,1,1,1,e+1,f): R2 (c=1=0+1, d=1=0+1)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- (1,1,0,0,e+2,f): R1 (a=1=0+1, b=1=0+1)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  finish

-- Main transition: (0,0,2,0,2p+1,3p+6) →⁺ (0,0,2,0,4p+5,6p+12)
theorem main_trans (p : ℕ) : ⟨0, 0, 2, 0, 2*p+1, 3*p+6⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2, 0, 4*p+5, 6*p+12⟩ := by
  -- Phase 1: (0,0,2,0,2p+1,3p+6) →* (0,0,0,0,2p+3,3p+4)
  -- Use phase1 with e=2p+1, f=3p+4 (so f+2 = 3p+6)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 0, 2*p+3, 3*p+4⟩)
  · have h := phase1 (2*p+1) (3*p+4)
    rw [show 3 * p + 4 + 2 = 3 * p + 6 from by ring,
        show 2 * p + 1 + 2 = 2 * p + 3 from by ring] at h
    exact h
  -- Phase 2: transfer f to (b,d)
  -- (0,0,0,0,2p+3,3p+4) →* (0,3p+4,0,3p+4,2p+3,0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*p+4, 0, 3*p+4, 2*p+3, 0⟩)
  · have h := f_to_bd (3*p+4) 0 0 (2*p+3) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5/R1/R1 loop
  -- (0,3p+4,0,3p+4,2p+3,0) →* (2,0,0,3p+4,p+1,0)
  -- 3p+4 = 3*(p+1)+1, 2p+3 = (p+1)+(p+1)+1
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 0, 0, 3*p+4, p+1, 0⟩)
  · have h := r5r1r1_loop (p+1) (3*p+4) (p+1)
    rw [show 3 * (p + 1) + 1 = 3 * p + 4 from by ring,
        show p + 1 + (p + 1) + 1 = 2 * p + 3 from by ring] at h
    exact h
  -- Phase 4: R3/R2 loop
  -- (2,0,0,3p+4,p+1,0) →* (2,0,0,0,4p+5,6p+8)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 0, 0, 0, 4*p+5, 6*p+8⟩)
  · have h := r3r2_loop (3*p+4) 0 (p+1) 0
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  -- Phase 5: two R3 steps
  -- (2,0,0,0,4p+5,6p+8) → (1,0,1,0,4p+5,6p+10) → (0,0,2,0,4p+5,6p+12)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 1, 6⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun p ↦ ⟨0, 0, 2, 0, 2*p+1, 3*p+6⟩) 0
  intro p
  refine ⟨2*p+2, ?_⟩
  show ⟨0, 0, 2, 0, 2*p+1, 3*p+6⟩ [fm]⊢⁺ ⟨0, 0, 2, 0, 2*(2*p+2)+1, 3*(2*p+2)+6⟩
  rw [show 2 * (2 * p + 2) + 1 = 4 * p + 5 from by ring,
      show 3 * (2 * p + 2) + 6 = 6 * p + 12 from by ring]
  exact main_trans p

end Sz22_2003_unofficial_193
