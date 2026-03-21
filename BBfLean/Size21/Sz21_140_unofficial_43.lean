import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #43: [35/6, 4/55, 121/2, 3/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_43

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: d → b (when a=0, c=0)
theorem d_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 repeated: a → e (when b=0, c=0)
theorem a_to_e : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 repeated: c,e → a (when b=0)
theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c+k, d, e+k⟩ [fm]⊢* ⟨a+2*k, 0, c, d, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Middle phase: from (2, b, C, D, C + F + b) to (2 + 2*C + b, 0, 0, D + b, F)
theorem middle_phase : ∀ b, ∀ C D F, ⟨2, b, C, D, C + F + b⟩ [fm]⊢* ⟨2 + 2*C + b, 0, 0, D + b, F⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro C D F
  rcases b with _ | _ | b
  · -- b = 0: just R2*C
    simp only [Nat.add_zero]
    -- goal: (2, 0, C, D, C + F) →* (2 + 2*C, 0, 0, D, F)
    -- r2_chain C: (2, 0, 0+C, D, F+C) →* (2+2*C, 0, 0, D, F)
    have h := r2_chain C 2 0 D F
    simp only [Nat.zero_add] at h
    rw [show C + F = F + C from by ring]
    exact h
  · -- b = 1: R1 then R2*(C+1)
    -- goal: (2, 1, C, D, C+F+1) →* (2+2*C+1, 0, 0, D+1, F)
    -- R1: (2, 1, C, D, C+F+1) → (1, 0, C+1, D+1, C+F+1)
    -- R2*(C+1): (1, 0, 0+(C+1), D+1, F+(C+1)) →* (1+2*(C+1), 0, 0, D+1, F)
    apply stepStar_trans (c₂ := ⟨1, 0, C + 1, D + 1, C + F + 1⟩)
    · show ⟨1 + 1, 0 + 1, C, D, C + F + 1⟩ [fm]⊢* ⟨1, 0, C + 1, D + 1, C + F + 1⟩
      apply step_stepStar; simp [fm]
    apply stepStar_trans (c₂ := ⟨1 + 2 * (C + 1), 0, 0, D + 1, F⟩)
    · have h := r2_chain (C + 1) 1 0 (D + 1) F
      simp only [Nat.zero_add] at h
      rw [show C + F + 1 = F + (C + 1) from by ring]
      exact h
    ring_nf; finish
  · -- b = b + 2: R1,R1,R2 then recurse
    -- (2, b+2, C, D, C+F+b+2) → R1 → (1, b+1, C+1, D+1, C+F+b+2)
    -- → R1 → (0, b, C+2, D+2, C+F+b+2) → R2 → (2, b, C+1, D+2, C+F+b+1)
    -- C+F+b+1 = (C+1)+F+b
    apply stepStar_trans (c₂ := ⟨2, b, C + 1, D + 2, (C + 1) + F + b⟩)
    · rw [show C + F + (b + 2) = C + F + b + 2 from by ring]
      apply stepStar_trans (c₂ := ⟨1, b + 1, C + 1, D + 1, C + F + b + 2⟩)
      · show ⟨1 + 1, (b + 1) + 1, C, D, C + F + b + 2⟩ [fm]⊢* ⟨1, b + 1, C + 1, D + 1, C + F + b + 2⟩
        apply step_stepStar; simp [fm]
      apply stepStar_trans (c₂ := ⟨0, b, C + 2, D + 2, C + F + b + 2⟩)
      · show ⟨0 + 1, b + 1, C + 1, D + 1, C + F + b + 2⟩ [fm]⊢* ⟨0, b, C + 2, D + 2, C + F + b + 2⟩
        apply step_stepStar; simp [fm]
      apply stepStar_trans (c₂ := ⟨2, b, C + 1, D + 2, C + F + b + 1⟩)
      · show ⟨0, b, (C + 1) + 1, D + 2, (C + F + b + 1) + 1⟩ [fm]⊢* ⟨2, b, C + 1, D + 2, C + F + b + 1⟩
        apply step_stepStar; simp [fm]
      rw [show C + F + b + 1 = (C + 1) + F + b from by ring]
      finish
    have h := ih b (by omega) (C + 1) (D + 2) F
    refine stepStar_trans h ?_
    ring_nf; finish

-- Full transition: (0, 0, 0, d, d+3+F) →⁺ (0, 0, 0, d+1, 2*d+6+F)
theorem main_trans : ∀ d F, ⟨0, 0, 0, d, d + 3 + F⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, d + 1, 2 * d + 6 + F⟩ := by
  intro d F
  -- Phase 1: R4*d → (0, d, 0, 0, d+3+F)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, d, 0, 0, d + 3 + F⟩)
  · have h := d_to_b d 0 0 (d + 3 + F)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5 step (gives ⊢⁺)
  apply step_stepStar_stepPlus (c₂ := ⟨0, d + 1, 1, 0, d + 2 + F⟩)
  · rw [show d + 3 + F = (d + 2 + F) + 1 from by ring]
    show fm ⟨0, d, 0, 0, (d + 2 + F) + 1⟩ = some ⟨0, d + 1, 1, 0, d + 2 + F⟩
    simp [fm]
  -- Now ⊢*: (0, d+1, 1, 0, d+2+F) →* (0, 0, 0, d+1, 2*d+6+F)
  -- Phase 3: R2 step
  apply stepStar_trans (c₂ := ⟨2, d + 1, 0, 0, d + 1 + F⟩)
  · rw [show d + 2 + F = (d + 1 + F) + 1 from by ring]
    apply step_stepStar
    show fm ⟨0, d + 1, 0 + 1, 0, (d + 1 + F) + 1⟩ = some ⟨2, d + 1, 0, 0, d + 1 + F⟩
    simp [fm]
  -- Phase 4: middle phase → (d+3, 0, 0, d+1, F)
  apply stepStar_trans (c₂ := ⟨d + 3, 0, 0, d + 1, F⟩)
  · have h := middle_phase (d + 1) 0 0 F
    simp only [Nat.zero_add] at h
    rw [show F + (d + 1) = d + 1 + F from by ring,
        show 2 + 2 * 0 + (d + 1) = d + 3 from by ring] at h
    exact h
  -- Phase 5: R3*(d+3) → (0, 0, 0, d+1, F+2*(d+3))
  have h := a_to_e (d + 3) 0 (d + 1) F
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) →* (0,0,0,1,5)
  -- (0,0,0,1,5) = (0,0,0,1, 1+3+1)
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 5⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d F, q = ⟨0, 0, 0, d, d + 3 + F⟩)
  · intro c ⟨d, F, hc⟩
    subst hc
    -- After transition: (0,0,0,d+1, 2*d+6+F) = (0,0,0,d+1, (d+1)+3+(d+2+F))
    exact ⟨⟨0, 0, 0, d + 1, 2 * d + 6 + F⟩,
           ⟨d + 1, d + 2 + F, by ring_nf⟩,
           main_trans d F⟩
  · exact ⟨1, 1, by ring_nf⟩
