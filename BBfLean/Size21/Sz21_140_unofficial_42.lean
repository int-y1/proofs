import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #42: [35/6, 4/55, 121/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_42

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: d → b (when a=0, c=0)
theorem r4_chain : ∀ k, ∀ b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 repeated: a → e+2 (when b=0, c=0)
theorem r3_chain : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 repeated: c,e → a+2 (when b=0)
theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+2*k, 0, c, d, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Interleaved phase: (1, b, c, d+1, e+b+c) →* (b+1+2*c, 0, 0, d+b+1, e)
-- by strong induction on b
theorem interleaved : ∀ b, ∀ c d e, ⟨1, b, c, d+1, e+b+c⟩ [fm]⊢* ⟨b+1+2*c, 0, 0, d+b+1, e⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c d e
  rcases b with _ | b
  · -- b=0: R2 chain (c steps)
    simp only [Nat.zero_add]
    have h := @r2_chain c 1 0 (d + 1) e
    simp only [Nat.zero_add] at h
    exact h
  rcases b with _ | b
  · -- b=1: R1 then R2 chain (c+1 steps)
    rw [show e + (0 + 1) + c = e + c + 1 from by ring,
        show 0 + 1 + 1 + 2 * c = 2 + 2 * c from by ring,
        show d + (0 + 1) + 1 = d + 2 from by ring]
    step fm
    rw [show d + 1 + 1 = d + 2 from by ring]
    have h := @r2_chain (c + 1) 0 0 (d + 2) e
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- b = b+2: R1, R2, R1 then induction
    rw [show e + (b + 1 + 1) + c = e + (b + c) + 1 + 1 from by ring,
        show b + 1 + 1 + 1 + 2 * c = b + 1 + 2 * (c + 1) from by ring,
        show d + (b + 1 + 1) + 1 = (d + 2) + b + 1 from by ring]
    -- R1: (1, (b+2), c, d+1, e+b+c+2) → (0, b+1, c+1, d+2, e+b+c+2)
    step fm
    rw [show d + 1 + 1 = d + 2 from by ring,
        show e + (b + c) + 1 + 1 = (e + (b + c) + 1) + 1 from by ring]
    -- R2: (0, b+1, c+1, d+2, e+b+c+2) → (2, b+1, c, d+2, e+b+c+1)
    step fm
    rw [show e + (b + c) + 1 = e + b + (c + 1) from by ring]
    -- R1: (2, b+1, c, d+2, e+b+c+1) → (1, b, c+1, d+3, e+b+c+1)
    step fm
    rw [show d + 2 + 1 = (d + 2) + 1 from by ring]
    exact ih b (by omega) (c + 1) (d + 2) e

-- Main transition: (0,0,0,d+1,e+d+2) →⁺ (0,0,0,d+2,e+2*d+4)
theorem main_trans (d e : ℕ) : ⟨0, 0, 0, d+1, e+d+2⟩ [fm]⊢⁺ ⟨0, 0, 0, d+2, e+2*d+4⟩ := by
  -- Phase 1: R4 x (d+1): →* (0,d+1,0,0,e+d+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, d+1, 0, 0, e+d+2⟩)
  · have h := @r4_chain (e + d + 2) (d + 1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step (provides the Plus): → (1,d+1,0,1,e+d+1)
  apply step_stepStar_stepPlus (c₂ := ⟨1, d+1, 0, 1, e+d+1⟩)
  · show fm ⟨0, d+1, 0, 0, (e+d+1)+1⟩ = some ⟨1, d+1, 0, 1, e+d+1⟩
    simp [fm]
  -- Phase 3: interleaved: →* (d+2, 0, 0, d+2, e)
  apply stepStar_trans (c₂ := ⟨d+2, 0, 0, d+2, e⟩)
  · have h := @interleaved (d+1) 0 0 e
    simp only [Nat.zero_add, Nat.add_zero] at h
    rw [show e + (d + 1) = e + d + 1 from by ring] at h
    exact h
  -- Phase 4: R3 x (d+2): →* (0, 0, 0, d+2, e+2*(d+2))
  have h := @r3_chain (d+2) 0 (d+2) e
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d+1, e+d+2⟩)
  · intro c ⟨d, e, hc⟩; subst hc
    refine ⟨_, ⟨d+1, e+d+1, rfl⟩, ?_⟩
    have h := main_trans d e
    rw [show d + 2 = d + 1 + 1 from by ring,
        show e + 2 * d + 4 = e + d + 1 + (d + 1) + 2 from by ring] at h
    exact h
  · exact ⟨0, 1, rfl⟩

end Sz21_140_unofficial_42
