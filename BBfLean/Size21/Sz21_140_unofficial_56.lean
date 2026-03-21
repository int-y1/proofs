import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #56: [35/6, 605/2, 4/77, 3/5, 7/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_56

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R1/R1/R3 round: (2, B+2, C, D, E+1) →+ (2, B, C+2, D+1, E)
theorem r1r1r3_round : ∀ B C D, ⟨2, B+2, C, D, E+1⟩ [fm]⊢⁺ ⟨2, B, C+2, D+1, E⟩ := by
  intro B C D
  step fm
  step fm
  rw [show C + 1 + 1 = C + 2 from by ring, show D + 1 + 1 = (D + 1) + 1 from by ring]
  step fm
  finish

-- k rounds of R1/R1/R3
theorem r1r1r3_rounds : ∀ k, ∀ B C D E, ⟨2, B+2*k, C, D, E+k⟩ [fm]⊢* ⟨2, B, C+2*k, D+k, E⟩ := by
  intro k; induction' k with k ih <;> intro B C D E
  · exists 0
  rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (@r1r1r3_round (E + k) (B + 2 * k) C D))
  have h2 := ih B (C + 2) (D + 1) E
  rw [show C + 2 + 2 * k = C + 2 * k + 2 from by ring] at h2
  refine stepStar_trans h2 ?_; ring_nf; finish

-- R1/R2/R3: (2, 1, C, D, E) →+ (2, 0, C+2, D, E+1)
theorem r1r2r3 : ∀ C D E, ⟨2, 1, C, D, E⟩ [fm]⊢⁺ ⟨2, 0, C+2, D, E+1⟩ := by
  intro C D E
  step fm; step fm
  rw [show C + 1 + 1 = C + 2 from by ring, show E + 2 = (E + 1) + 1 from by ring]
  step fm; finish

-- R2/R2/R3: (2, 0, C, D+1, E) →+ (2, 0, C+2, D, E+3)
theorem r2r2r3 : ∀ C D E, ⟨2, 0, C, D+1, E⟩ [fm]⊢⁺ ⟨2, 0, C+2, D, E+3⟩ := by
  intro C D E
  step fm; step fm
  rw [show C + 1 + 1 = C + 2 from by ring, show E + 2 + 2 = (E + 3) + 1 from by ring]
  step fm; finish

-- k rounds of R2/R2/R3
theorem r2r2r3_rounds : ∀ k, ∀ C D E, ⟨2, 0, C, D+k, E⟩ [fm]⊢* ⟨2, 0, C+2*k, D, E+3*k⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · exists 0
  rw [show D + (k + 1) = (D + k) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (r2r2r3 C (D + k) E))
  have h2 := ih (C + 2) D (E + 3)
  rw [show C + 2 + 2 * k = C + 2 * k + 2 from by ring,
      show E + 3 + 3 * k = E + 3 * k + 3 from by ring] at h2
  refine stepStar_trans h2 ?_; ring_nf; finish

-- R2/R2 final: (2, 0, C, 0, E) →* (0, 0, C+2, 0, E+4)
theorem r2r2_final : ∀ C E, ⟨2, 0, C, 0, E⟩ [fm]⊢* ⟨0, 0, C+2, 0, E+4⟩ := by
  intro C E
  step fm; step fm
  rw [show C + 1 + 1 = C + 2 from by ring, show E + 2 + 2 = E + 4 from by ring]
  finish

-- R4 repeated: c → b
theorem c_to_b : ∀ k, ∀ b, ⟨0, b, k, 0, e⟩ [fm]⊢* ⟨0, b+k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  rw [show b + (k + 1) = (b + 1) + k from by ring]
  step fm; apply stepStar_trans (ih _); ring_nf; finish

-- Even case main transition
theorem main_trans_even (k E : ℕ) : ⟨0, 2*k+1, 0, 0, E+k+1⟩ [fm]⊢⁺ ⟨0, 4*k+2, 0, 0, E+3*k+4⟩ := by
  -- Phase 1: R5 → R3
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*k, 0, 1, E+k+1⟩)
  · show fm ⟨0, (2*k)+1, 0, 0, E+k+1⟩ = some ⟨0, 2*k, 0, 1, E+k+1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨2, 2*k, 0, 0, E+k⟩)
  · rw [show E + k + 1 = (E + k) + 1 from by ring]
    step fm; finish
  -- Phase 2: R1/R1/R3 rounds
  apply stepStar_trans (c₂ := ⟨2, 0, 2*k, k, E⟩)
  · have h := r1r1r3_rounds k 0 0 0 E
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R2/R2/R3 rounds
  apply stepStar_trans (c₂ := ⟨2, 0, 4*k, 0, E+3*k⟩)
  · have h := r2r2r3_rounds k (2*k) 0 E
    rw [show 2*k + 2*k = 4*k from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 4: R2/R2 final
  apply stepStar_trans (c₂ := ⟨0, 0, 4*k+2, 0, E+3*k+4⟩)
  · exact r2r2_final (4*k) (E+3*k)
  -- Phase 5: c → b
  have h := c_to_b (4*k+2) 0 (e := E+3*k+4)
  simp only [Nat.zero_add] at h; exact h

-- Odd case main transition
theorem main_trans_odd (k E : ℕ) : ⟨0, 2*k+2, 0, 0, E+k+1⟩ [fm]⊢⁺ ⟨0, 4*k+4, 0, 0, E+3*k+5⟩ := by
  -- Phase 1: R5 → R3
  apply step_stepStar_stepPlus (c₂ := ⟨0, 2*k+1, 0, 1, E+k+1⟩)
  · show fm ⟨0, (2*k+1)+1, 0, 0, E+k+1⟩ = some ⟨0, 2*k+1, 0, 1, E+k+1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨2, 2*k+1, 0, 0, E+k⟩)
  · rw [show E + k + 1 = (E + k) + 1 from by ring]
    step fm; finish
  -- Phase 2: R1/R1/R3 rounds
  apply stepStar_trans (c₂ := ⟨2, 1, 2*k, k, E⟩)
  · have h := r1r1r3_rounds k 1 0 0 E
    simp only [Nat.zero_add] at h
    rw [show 1 + 2*k = 2*k+1 from by ring] at h; exact h
  -- Phase 3: R1/R2/R3
  apply stepStar_trans (c₂ := ⟨2, 0, 2*k+2, k, E+1⟩)
  · exact stepPlus_stepStar (r1r2r3 (2*k) k E)
  -- Phase 4: R2/R2/R3 rounds
  apply stepStar_trans (c₂ := ⟨2, 0, 4*k+2, 0, E+3*k+1⟩)
  · have h := r2r2r3_rounds k (2*k+2) 0 (E+1)
    rw [show 2*k+2 + 2*k = 4*k+2 from by ring,
        show E+1 + 3*k = E+3*k+1 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase 5: R2/R2 final
  apply stepStar_trans (c₂ := ⟨0, 0, 4*k+4, 0, E+3*k+5⟩)
  · exact r2r2_final (4*k+2) (E+3*k+1)
  -- Phase 6: c → b
  have h := c_to_b (4*k+4) 0 (e := E+3*k+5)
  simp only [Nat.zero_add] at h; exact h

-- Combined main transition
theorem main_trans (b e : ℕ) : ⟨0, b+1, 0, 0, e+b+2⟩ [fm]⊢⁺ ⟨0, 2*b+2, 0, 0, e+2*b+5⟩ := by
  rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2*k from by ring] at hk; subst hk
    have h := main_trans_even k (e+k+1)
    convert h using 2 ; ring_nf
  · subst hk
    have h := main_trans_odd k (e+k+2)
    convert h using 2 ; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 2⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨b, e⟩ ↦ ⟨0, b+1, 0, 0, e+b+2⟩) ⟨0, 0⟩
  intro ⟨b, e⟩
  refine ⟨⟨2*b+1, e+2⟩, ?_⟩
  show ⟨0, b+1, 0, 0, e+b+2⟩ [fm]⊢⁺ ⟨0, (2*b+1)+1, 0, 0, (e+2)+(2*b+1)+2⟩
  convert main_trans b e using 2 ; ring_nf
