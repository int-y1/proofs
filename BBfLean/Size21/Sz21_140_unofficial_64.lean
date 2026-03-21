import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #64: [4/15, 33/14, 25/2, 7/11, 22/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_64

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- Phase 2: R2/R1 chain. Each round: (a'+1, 0, c'+1, d'+1, e') -R2-> -R1-> (a'+2, 0, c', d', e'+1)
-- Net per round on (a,c,d,e): (+1, -1, -1, +1)
-- After D rounds: (a+1, 0, c+D, D, e) →* (a+D+1, 0, c, 0, e+D)
theorem r2r1_chain : ∀ D, ∀ a c e, ⟨a+1, 0, c+D, D, e⟩ [fm]⊢* ⟨a+D+1, 0, c, 0, e+D⟩ := by
  intro D; induction' D with D ih <;> intro a c e
  · exists 0
  rw [show c + (D + 1) = (c + D) + 1 from by ring]
  -- State: (a+1, 0, (c+D)+1, D+1, e)
  -- R2: a+1 >= 1, d = D+1 >= 1 → (a, 1, (c+D)+1, D, e+1)
  -- But wait, R1 fires first if b+1 and c+1... b=0 so R1 doesn't fire. R2 fires.
  step fm
  -- State after R2: (a, 0+1, (c+D)+1, D, e+1) but with b=1, c+D+1 >= 1
  -- R1: (a+2, 0, c+D, D, e+1)
  step fm
  -- Now state: (a+2, 0, c+D, D, e+1). Apply ih with a' = a+1, e' = e+1
  have h := ih (a+1) c (e+1)
  rw [show a + 1 + 1 = a + 2 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Phase 3: R3 repeated. (a+k, 0, c, 0, e) →* (a, 0, c+2*k, 0, e)
-- R3 fires when a >= 1, b = 0, d = 0 (and R1/R2 don't match since b=0, d=0)
theorem r3_chain : ∀ k, ∀ a c, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+2*k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 4: R4 repeated. (0, 0, c, d, e+k) →* (0, 0, c, d+k, e)
-- R4 fires when a=0, b=0, c can be anything but R5 needs c>=1 and e=0... wait
-- R4: (a, b, c, d, e+1) → (a, b, c, d+1, e) — fires when no earlier rule matches
-- With a=0, b=0: R1 needs b>=1 (no), R2 needs a>=1 (no), R3 needs a>=1 (no), R4 needs e>=1
theorem r4_chain : ∀ k, ∀ d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  rw [show k + 1 = (k) + 1 from rfl]
  step fm
  apply stepStar_trans (ih _)
  ring_nf; finish

-- Main transition: (0, 0, r+d+1, d, 0) ⊢⁺ (0, 0, r+2*d+2, d+1, 0)
theorem main_trans (r d : ℕ) :
    ⟨0, 0, r + d + 1, d, 0⟩ [fm]⊢⁺ ⟨0, 0, r + 2 * d + 2, d + 1, 0⟩ := by
  -- Phase 1: R5 step
  rw [show r + d + 1 = (r + d) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (r + d) + 1, d, 0⟩ = some ⟨1, 0, r + d, d, 1⟩
    simp [fm]
  -- State: (1, 0, r+d, d, 1)
  -- Phase 2: d rounds of R2/R1
  apply stepStar_trans (c₂ := ⟨d + 1, 0, r, 0, d + 1⟩)
  · have h2 := r2r1_chain d 0 r 1
    simp only [Nat.zero_add] at h2
    convert h2 using 2; ring_nf
  -- State: (d+1, 0, r, 0, d+1)
  -- Phase 3: (d+1) R3 steps
  apply stepStar_trans (c₂ := ⟨0, 0, r + 2 * (d + 1), 0, d + 1⟩)
  · have h3 := r3_chain (e := d + 1) (d + 1) 0 r
    simp only [Nat.zero_add] at h3; exact h3
  -- State: (0, 0, r + 2*(d+1), 0, d+1)
  -- Phase 4: (d+1) R4 steps
  have h4 := r4_chain (c := r + 2 * (d + 1)) (d + 1) 0
  simp only [Nat.zero_add] at h4
  refine stepStar_trans h4 ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1, 0, 0, 0, 0) →* (0, 0, 2, 0, 0) in 1 step (R3)
  -- (0, 0, 2, 0, 0) = (0, 0, 1 + 0 + 1, 0, 0) with r=1, d=0
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨r, d⟩ ↦ ⟨0, 0, r + d + 1, d, 0⟩) ⟨1, 0⟩
  intro ⟨r, d⟩
  refine ⟨⟨r + d, d + 1⟩, ?_⟩
  have h := main_trans r d
  -- Need: (0, 0, r+d+1, d, 0) ⊢⁺ (0, 0, (r+d)+(d+1)+1, d+1, 0)
  -- main_trans gives: (0, 0, r+d+1, d, 0) ⊢⁺ (0, 0, r+2*d+2, d+1, 0)
  -- (r+d)+(d+1)+1 = r+2*d+2 ✓
  convert h using 2; ring_nf

end Sz21_140_unofficial_64
