import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #85: [5/6, 49/2, 44/35, 9/11, 5/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  2  0  0 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_85

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- Phase 1: R4 repeated: e → b (when a=0, c=0)
theorem e_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d, e+k⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 4: R2,R2,R3 repeated: (2, 0, c+k, d, e) →* (2, 0, c, d+3*k, e+k)
theorem r2r2r3_chain : ∀ k, ∀ c d e, ⟨2, 0, c+k, d, e⟩ [fm]⊢* ⟨2, 0, c, d+3*k, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = c + k + 1 from by ring]
  -- State: (2, 0, c+k+1, d, e)
  -- R2: a=2>=1, b=0, so R2: (1, 0, c+k+1, d+2, e)
  step fm
  -- R2: a=1>=1, b=0, so R2: (0, 0, c+k+1, d+4, e)
  step fm
  -- R3: c+k+1>=1, d+4>=1: (2, 0, c+k, d+3, e+1)
  rw [show c + k + 1 = (c + k) + 1 from by ring,
      show d + 4 = (d + 3) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phase 3: one R1,R1,R3 round
-- From (2, b+2, c, d+1, e) via R1→(1,b+1,c+1,d+1,e), R1→(0,b,c+2,d+1,e), R3→(2,b,c+1,d,e+1)
-- Actually let's do the chain directly
theorem r1r1r3_chain : ∀ k, ∀ b c d e, ⟨2, b+2*k, c, d+k, e+1⟩ [fm]⊢* ⟨2, b, c+k, d, e+k+1⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · exists 0
  -- Goal: (2, b+2*(k+1), c, d+(k+1), e+1) →* (2, b, c+(k+1), d, e+(k+1)+1)
  -- Rewrite LHS
  rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
      show d + (k + 1) = d + k + 1 from by ring]
  -- R1: a+1=2+1? No, a+1, b+1 pattern. State is (2, (b+2*k+1)+1, c, d+k+1, e+1)
  -- = (1+1, (b+2*k+1)+1, c, d+k+1, e+1) matches R1
  step fm
  -- Now: (1, b+2*k+1, c+1, d+k+1, e+1)
  -- = (0+1, (b+2*k)+1, c+1, d+k+1, e+1) matches R1
  rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
  step fm
  -- Now: (0, b+2*k, c+2, d+k+1, e+1)
  -- = (0, b+2*k, (c+1)+1, (d+k)+1, e+1) matches R3
  rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
      show d + k + 1 = (d + k) + 1 from by ring]
  step fm
  -- Now: (2, b+2*k, c+1, d+k, e+2)
  -- Need: →* (2, b, c+(k+1), d, e+(k+1)+1)
  -- = (2, b+2*k, c+1, d+k, (e+1)+1) and IH gives →* (2, b, c+1+k, d, (e+1)+k+1)
  rw [show e + 1 + 1 = (e + 1) + 1 from by ring]
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Final: R2,R2: (2, 0, 0, d, e) →* (0, 0, 0, d+4, e)
theorem final_r2r2 : ⟨2, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d+4, e⟩ := by
  step fm; step fm; ring_nf; finish

-- Main transition: (0, 0, 0, 2*e+2, e) ⊢⁺ (0, 0, 0, 4*e+4, 2*e+1)
theorem main_trans : ⟨0, 0, 0, 2*e+2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*e+4, 2*e+1⟩ := by
  -- Phase 1: R4 × e: (0, 0, 0, 2*e+2, e) →* (0, 2*e, 0, 2*e+2, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*e, 0, 2*e+2, 0⟩)
  · have h := e_to_b e 0 (2*e+2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 then R3
  -- (0, 2*e, 0, 2*e+2, 0): a=0, c=0, e=0, d=2*e+2>=1 → R5: (0, 2*e, 1, 2*e+1, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*e, 1, 2*e+1, 0⟩)
  · show fm ⟨0, 2 * e, 0, (2 * e + 1) + 1, 0⟩ = some ⟨0, 2 * e, 0 + 1, 2 * e + 1, 0⟩
    simp [fm]
  -- (0, 2*e, 1, 2*e+1, 0): a=0, c=1>=1, d=2*e+1>=1 → R3: (2, 2*e, 0, 2*e, 1)
  apply stepStar_trans (c₂ := ⟨2, 2*e, 0, 2*e, 1⟩)
  · rw [show 2 * e + 1 = (2 * e) + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    finish
  -- Phase 3: R1,R1,R3 × e rounds: (2, 2*e, 0, 2*e, 1) →* (2, 0, e, e, e+1)
  apply stepStar_trans (c₂ := ⟨2, 0, e, e, e+1⟩)
  · have h := r1r1r3_chain e 0 0 e 0
    simp only [Nat.zero_add] at h
    rw [show 2 * e = 0 + 2 * e from by ring,
        show e = 0 + e from by ring] at h ⊢
    convert h using 2; ring_nf
  -- Phase 4: R2,R2,R3 × e rounds: (2, 0, e, e, e+1) →* (2, 0, 0, 4*e, 2*e+1)
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 4*e, 2*e+1⟩)
  · have h := r2r2r3_chain e 0 e (e+1)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  -- Phase 5: R2,R2: (2, 0, 0, 4*e, 2*e+1) →* (0, 0, 0, 4*e+4, 2*e+1)
  exact final_r2r2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨0, 0, 0, 2*e+2, e⟩) 0
  intro e; refine ⟨2*e+1, ?_⟩
  have h := @main_trans e
  convert h using 2; ring_nf
