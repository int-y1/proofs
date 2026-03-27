import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #28: [1/15, 2/21, 4719/2, 35/11, 9/65]

Vector representation:
```
 0 -1 -1  0  0  0
 1 -1  0 -1  0  0
-1  1  0  0  2  1
 0  0  1  1 -1  0
 0  2 -1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_28

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b+1, c, d+1, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+2, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a, b+2, c, d, e, f⟩
  | _ => none

-- R4 chain: e transfers to c and d
theorem r4_chain : ∀ k c d f,
    ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c+k, d+k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  step fm
  apply stepStar_trans (ih (c + 1) (d + 1) f)
  ring_nf; finish

-- R5, R1, R1 rounds: each round decreases c by 3 and f by 1
-- (0, 0, c+3, D, 0, f+1) →* (0, 0, c, D, 0, f) [one round]
-- We do k rounds: (0, 0, c+3k, D, 0, f+k) →* (0, 0, c, D, 0, f)
theorem r5r1r1_chain : ∀ k c D f,
    ⟨0, 0, c+3*(k+1), D, 0, f+k+1⟩ [fm]⊢* ⟨0, 0, c, D, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c D f
  · -- k=0: one round (0,0,c+3,D,0,f+1) →3 (0,0,c,D,0,f)
    rw [show c + 3 * 1 = (c + 2) + 1 from by ring, show f + 0 + 1 = f + 1 from by ring]
    step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    step fm
    rw [show c + 1 = c + 1 from rfl]
    step fm; finish
  -- k+1: do one round then apply ih
  rw [show c + 3 * (k + 1 + 1) = (c + 3 * (k + 1)) + 2 + 1 from by ring,
      show f + (k + 1) + 1 = (f + k + 1) + 1 from by ring]
  step fm
  rw [show (c + 3 * (k + 1)) + 2 = (c + 3 * (k + 1)) + 1 + 1 from by ring]
  step fm
  rw [show (c + 3 * (k + 1)) + 1 = (c + 3 * (k + 1)) + 1 from rfl]
  step fm
  exact ih c D f

-- R3, R2 pairs: d drains while e and f grow
theorem r3r2_chain : ∀ k d e f,
    ⟨2, 0, 0, d+k, e, f⟩ [fm]⊢* ⟨2, 0, 0, d, e+2*k, f+k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih d (e + 2) (f + 1))
  ring_nf; finish

-- Main transition: (2, 0, 0, 0, 6*n, 4*n) →⁺ (2, 0, 0, 0, 6*(2*n+1), 4*(2*n+1))
theorem main_trans (n : ℕ) :
    ⟨2, 0, 0, 0, 6*n, 4*n⟩ [fm]⊢⁺ ⟨2, 0, 0, 0, 6*(2*n+1), 4*(2*n+1)⟩ := by
  -- Phase 1: R3 x2
  apply step_stepStar_stepPlus (c₂ := ⟨1, 1, 0, 0, 6*n+2, 4*n+1⟩)
  · show fm ⟨1+1, 0, 0, 0, 6*n, 4*n⟩ = some ⟨1, 1, 0, 0, 6*n+2, 4*n+1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 2, 0, 0, 6*n+4, 4*n+2⟩)
  · apply step_stepStar
    show fm ⟨0+1, 1, 0, 0, 6*n+2, 4*n+1⟩ = some ⟨0, 2, 0, 0, 6*n+4, 4*n+2⟩; simp [fm]
  -- Phase 2: R4, R1, R2 (3 steps)
  apply stepStar_trans (c₂ := ⟨0, 2, 1, 1, 6*n+3, 4*n+2⟩)
  · apply step_stepStar
    rw [show (6*n+4 : ℕ) = (6*n+3)+1 from by ring]
    show fm ⟨0, 2, 0, 0, (6*n+3)+1, 4*n+2⟩ = some ⟨0, 2, 1, 1, 6*n+3, 4*n+2⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 1, 0, 1, 6*n+3, 4*n+2⟩)
  · apply step_stepStar
    show fm ⟨0, 1+1, 0+1, 1, 6*n+3, 4*n+2⟩ = some ⟨0, 1, 0, 1, 6*n+3, 4*n+2⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨1, 0, 0, 0, 6*n+3, 4*n+2⟩)
  · apply step_stepStar
    show fm ⟨0, 0+1, 0, 0+1, 6*n+3, 4*n+2⟩ = some ⟨0+1, 0, 0, 0, 6*n+3, 4*n+2⟩; simp [fm]
  -- Phase 3: R3
  apply stepStar_trans (c₂ := ⟨0, 1, 0, 0, 6*n+5, 4*n+3⟩)
  · apply step_stepStar
    show fm ⟨0+1, 0, 0, 0, 6*n+3, 4*n+2⟩ = some ⟨0, 1, 0, 0, 6*n+5, 4*n+3⟩; simp [fm]
  -- Phase 4: R4, R1
  apply stepStar_trans (c₂ := ⟨0, 1, 1, 1, 6*n+4, 4*n+3⟩)
  · apply step_stepStar
    rw [show (6*n+5 : ℕ) = (6*n+4)+1 from by ring]
    show fm ⟨0, 1, 0, 0, (6*n+4)+1, 4*n+3⟩ = some ⟨0, 1, 1, 1, 6*n+4, 4*n+3⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 1, 6*n+4, 4*n+3⟩)
  · apply step_stepStar
    show fm ⟨0, 0+1, 0+1, 1, 6*n+4, 4*n+3⟩ = some ⟨0, 0, 0, 1, 6*n+4, 4*n+3⟩; simp [fm]
  -- Phase 5: R4 chain: (0,0,0,1,6n+4,4n+3) → (0,0,6n+4,6n+5,0,4n+3)
  apply stepStar_trans (c₂ := ⟨0, 0, 6*n+4, 6*n+5, 0, 4*n+3⟩)
  · have h := r4_chain (6*n+4) 0 1 (4*n+3)
    rw [show 0 + (6*n+4) = 6*n+4 from by ring, show 1 + (6*n+4) = 6*n+5 from by ring] at h
    exact h
  -- Phase 6: R5,R1,R1 chain: (0,0,6n+4,6n+5,0,4n+3) → (0,0,1,6n+5,0,2n+2)
  -- 6n+4 = 1 + 3*(2n+1), 4n+3 = (2n+2) + (2n+1)
  apply stepStar_trans (c₂ := ⟨0, 0, 1, 6*n+5, 0, 2*n+2⟩)
  · have h := r5r1r1_chain (2*n) 1 (6*n+5) (2*n+2)
    rw [show 1 + 3 * (2*n + 1) = 6*n+4 from by ring,
        show (2*n+2) + 2*n + 1 = 4*n+3 from by ring] at h
    exact h
  -- Final R5: (0,0,1,6n+5,0,2n+2) → (0,2,0,6n+5,0,2n+1)
  apply stepStar_trans (c₂ := ⟨0, 2, 0, 6*n+5, 0, 2*n+1⟩)
  · apply step_stepStar
    rw [show (2*n+2 : ℕ) = (2*n+1)+1 from by ring]
    show fm ⟨0, 0, 0+1, 6*n+5, 0, (2*n+1)+1⟩ = some ⟨0, 0+2, 0, 6*n+5, 0, 2*n+1⟩; simp [fm]
  -- Phase 7: R2 x2: (0,2,0,6n+5,0,2n+1) → (2,0,0,6n+3,0,2n+1)
  apply stepStar_trans (c₂ := ⟨1, 1, 0, 6*n+4, 0, 2*n+1⟩)
  · apply step_stepStar
    rw [show (6*n+5 : ℕ) = (6*n+4)+1 from by ring]
    show fm ⟨0, 1+1, 0, (6*n+4)+1, 0, 2*n+1⟩ = some ⟨0+1, 1, 0, 6*n+4, 0, 2*n+1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨2, 0, 0, 6*n+3, 0, 2*n+1⟩)
  · apply step_stepStar
    rw [show (6*n+4 : ℕ) = (6*n+3)+1 from by ring]
    show fm ⟨1, 0+1, 0, (6*n+3)+1, 0, 2*n+1⟩ = some ⟨1+1, 0, 0, 6*n+3, 0, 2*n+1⟩; simp [fm]
  -- Phase 8: R3,R2 chain: (2,0,0,6n+3,0,2n+1) → (2,0,0,0,12n+6,8n+4)
  have h := r3r2_chain (6*n+3) 0 0 (2*n+1)
  rw [show 0 + (6*n+3) = 6*n+3 from by ring, show 0 + 2*(6*n+3) = 12*n+6 from by ring,
      show (2*n+1) + (6*n+3) = 8*n+4 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2, 0, 0, 0, 6*n, 4*n⟩) 0
  intro n; exact ⟨2*n+1, main_trans n⟩

end Sz22_2003_unofficial_28
