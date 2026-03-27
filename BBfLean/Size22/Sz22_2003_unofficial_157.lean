import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #157: [1/45, 35/2, 26/55, 363/7, 5/39]

Vector representation:
```
 0 -2 -1  0  0  0
-1  0  1  1  0  0
 1  0 -1  0 -1  1
 0  1  0 -1  2  0
 0 -1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_157

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+2, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- Phase B: alternating R3 & R2, consuming e and building d and f
-- (0, 0, 1, d, e+k, f) ->* (0, 0, 1, d+k, e, f+k)
theorem r3r2_chain : ∀ k, ∀ d e f, ⟨0, 0, 1, d, e+k, f⟩ [fm]⊢* ⟨0, 0, 1, d+k, e, f+k⟩ := by
  intro k; induction' k with k h <;> intro d e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  -- R3: (0, 0, 1, d, (e+k)+1, f) -> (1, 0, 0, d, e+k, f+1)
  step fm
  -- R2: (1, 0, 0, d, e+k, f+1) -> (0, 0, 1, d+1, e+k, f+1)
  step fm
  apply stepStar_trans (h (d+1) e (f+1))
  ring_nf; finish

-- Phase D: R4 repeated, draining d and building b and e
-- (0, b, 0, d+k, e, f) ->* (0, b+k, 0, d, e+2*k, f)
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e+2*k, f⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  -- R4: (0, b, 0, (d+k)+1, e, f) -> (0, b+1, 0, d+k, e+2, f)
  step fm
  apply stepStar_trans (h (b+1) d (e+2))
  ring_nf; finish

-- Phase E: pairs of R5 & R1, reducing b by 3 and f by 1 each
-- (0, 3*k+1, 0, 0, e, f+k) ->* (0, 1, 0, 0, e, f)
theorem r5r1_chain : ∀ k, ∀ e f, ⟨0, 3*k+1, 0, 0, e, f+k⟩ [fm]⊢* ⟨0, 1, 0, 0, e, f⟩ := by
  intro k; induction' k with k h <;> intro e f
  · exists 0
  rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 3 from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  -- State: (0, (3k+1)+3, 0, 0, e, (f+k)+1)
  -- = (0, 3k+4, 0, 0, e, f+k+1)
  -- R5: b+1 = 3k+4, f+1 = f+k+1 -> (0, 3k+3, 1, 0, e, f+k)
  step fm
  -- R1: b+2 = 3k+3 so b = 3k+1, c+1 = 1 -> (0, 3k+1, 0, 0, e, f+k)
  step fm
  apply stepStar_trans (h e f)
  ring_nf; finish

-- Main transition: (1, 0, 0, 0, 3*m, 2*m) ->+ (1, 0, 0, 0, 6*m+3, 4*m+2)
theorem main_trans (m : ℕ) : ⟨1, 0, 0, 0, 3*m, 2*m⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 6*m+3, 4*m+2⟩ := by
  -- Phase A: R2: (1, 0, 0, 0, 3m, 2m) -> (0, 0, 1, 1, 3m, 2m)
  step fm
  -- Phase B: r3r2_chain with k=3m: (0, 0, 1, 1, 3m, 2m) ->* (0, 0, 1, 3m+1, 0, 5m)
  apply stepStar_trans (c₂ := ⟨0, 0, 1, 3*m+1, 0, 5*m⟩)
  · have h := r3r2_chain (3*m) 1 0 (2*m)
    simp only [Nat.zero_add] at h
    rw [show 1 + 3 * m = 3 * m + 1 from by ring,
        show 2 * m + 3 * m = 5 * m from by ring] at h
    exact h
  -- Phase C: 7 steps: (0,0,1,3m+1,0,5m) -> (0,0,0,3m+1,2,5m+2)
  -- R4: (0,0,1,3m+1,0,5m) -> (0,1,1,3m,2,5m) -- needs 3m+1>=1
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 3*m+1, 2, 5*m+2⟩)
  · rw [show 3 * m + 1 = 3 * m + 1 from rfl]
    -- need to show (0,0,1,(3m)+1,0,5m) matches R4 which needs d+1
    -- Actually (0,0,1,3m+1,0,5m): c=1, no b>=2. a=0. c=1 but e=0 so R3 fails. d=3m+1>=1 so R4.
    step fm
    -- (0,1,1,3m,2,5m): R1? b=1 < 2 no. R2? a=0 no. R3: c=1, e=2>=1 yes.
    step fm
    -- (1,1,0,3m,1,5m+1): R2: a=1.
    step fm
    -- (0,1,1,3m+1,1,5m+1): R3: c=1, e=1.
    step fm
    -- (1,1,0,3m+1,0,5m+2): R2: a=1.
    step fm
    -- (0,1,1,3m+2,0,5m+2): R4: d=3m+2>=1.
    step fm
    -- (0,2,1,3m+1,2,5m+2): R1: b=2>=2, c=1>=1.
    step fm
    finish
  -- Phase D: r4_chain with k=3m+1: (0,0,0,3m+1,2,5m+2) ->* (0,3m+1,0,0,6m+4,5m+2)
  apply stepStar_trans (c₂ := ⟨0, 3*m+1, 0, 0, 6*m+4, 5*m+2⟩)
  · have h := r4_chain (f := 5*m+2) (3*m+1) 0 0 2
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * (3 * m + 1) = 6 * m + 4 from by ring] at h
    exact h
  -- Phase E: r5r1_chain with k=m: (0,3m+1,0,0,6m+4,5m+2) ->* (0,1,0,0,6m+4,4m+2)
  apply stepStar_trans (c₂ := ⟨0, 1, 0, 0, 6*m+4, 4*m+2⟩)
  · have h := r5r1_chain m (6*m+4) (4*m+2)
    rw [show 3 * m + 1 = 3 * m + 1 from rfl,
        show 4 * m + 2 + m = 5 * m + 2 from by ring] at h
    exact h
  -- Phase F: R5 then R3: (0,1,0,0,6m+4,4m+2) -> (0,0,1,0,6m+4,4m+1) -> (1,0,0,0,6m+3,4m+2)
  step fm
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun m ↦ ⟨1, 0, 0, 0, 3*m, 2*m⟩) 0
  intro m
  refine ⟨2*m+1, ?_⟩
  rw [show 3 * (2 * m + 1) = 6 * m + 3 from by ring,
      show 2 * (2 * m + 1) = 4 * m + 2 from by ring]
  exact main_trans m

end Sz22_2003_unofficial_157
