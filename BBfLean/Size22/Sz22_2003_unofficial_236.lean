import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #236: [11/105, 20/3, 3/22, 7/2, 99/7]

Vector representation:
```
 0 -1 -1 -1  1
 2 -1  1  0  0
-1  1  0  0 -1
-1  0  0  1  0
 0  2  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_236

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R4 chain: drain a into d
theorem a_to_d : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a c (d + 1))
  ring_nf; finish

-- R5/R1/R1 chain
theorem r5r1r1 : ∀ k c d e, ⟨0, 0, c+2*k, d+3*k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+3*k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
      show d + 3 * (k + 1) = (d + 3 * k) + 3 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih c d (e + 3))
  ring_nf; finish

-- R2 steps for symbolic c
theorem r2_b1 (c e : ℕ) : (⟨0, 1, c, 0, e⟩ : Q) [fm]⊢ ⟨2, 0, c+1, 0, e⟩ := by
  rcases c with _ | c <;> simp [fm]

theorem r2_b2 (c e : ℕ) : (⟨0, 2, c, 0, e⟩ : Q) [fm]⊢ ⟨2, 1, c+1, 0, e⟩ := by
  rcases c with _ | c <;> simp [fm]

theorem r2_ab1 (a c e : ℕ) : (⟨a, 1, c, 0, e⟩ : Q) [fm]⊢ ⟨a+2, 0, c+1, 0, e⟩ := by
  rcases c with _ | c <;> simp [fm]

-- R3/R2 chain
theorem r3r2 : ∀ k a c e, ⟨a+1, 0, c, 0, e+k⟩ [fm]⊢* ⟨a+1+k, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih (a + 1) (c + 1) e)
  ring_nf; finish

-- Even->Odd: (6k+5, 0, 2k²+6k+3, 0, 0) ⊢⁺ (6k+7, 0, 2k²+8k+6, 0, 0)
theorem even_to_odd (k : ℕ) :
    ⟨6*k+5, 0, 2*k^2+6*k+3, 0, 0⟩ [fm]⊢⁺ ⟨6*k+7, 0, 2*k^2+8*k+6, 0, 0⟩ := by
  -- Phase 1: a → d
  apply stepStar_stepPlus_stepPlus
  · show ⟨6*k+5, 0, 2*k^2+6*k+3, 0, 0⟩ [fm]⊢* ⟨0, 0, 2*k^2+6*k+3, 6*k+5, 0⟩
    have h := a_to_d (6*k+5) 0 (2*k^2+6*k+3) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5/R1/R1
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 2*k^2+6*k+3, 6*k+5, 0⟩ [fm]⊢* ⟨0, 0, 2*k^2+2*k+1, 2, 6*k+3⟩
    have h := r5r1r1 (2*k+1) (2*k^2+2*k+1) 2 0
    rw [show 2*k^2+2*k+1+2*(2*k+1) = 2*k^2+6*k+3 from by ring,
        show 2+3*(2*k+1) = 6*k+5 from by ring,
        show 0+3*(2*k+1) = 6*k+3 from by ring] at h; exact h
  -- Phase 3: R5+R1+R2
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 2*k^2+2*k+1, 2, 6*k+3⟩ [fm]⊢* ⟨0, 1, 2*k^2+2*k, 0, 6*k+5⟩
    apply stepStar_trans (c₂ := ⟨0, 2, 2*k^2+2*k+1, 1, 6*k+4⟩)
    · exact step_stepStar (show fm ⟨0, 0, 2*k^2+2*k+1, 2, 6*k+3⟩ = some ⟨0, 2, 2*k^2+2*k+1, 1, 6*k+4⟩
        from by simp [fm])
    · exact step_stepStar (show fm ⟨0, 2, 2*k^2+2*k+1, 1, 6*k+4⟩ = some ⟨0, 1, 2*k^2+2*k, 0, 6*k+5⟩
        from by simp [fm])
  apply step_stepStar_stepPlus
  · show ⟨0, 1, 2*k^2+2*k, 0, 6*k+5⟩ [fm]⊢ ⟨2, 0, 2*k^2+2*k+1, 0, 6*k+5⟩
    exact r2_b1 _ _
  -- Phase 4: R3/R2
  show ⟨2, 0, 2*k^2+2*k+1, 0, 6*k+5⟩ [fm]⊢* ⟨6*k+7, 0, 2*k^2+8*k+6, 0, 0⟩
  have h := r3r2 (6*k+5) 1 (2*k^2+2*k+1) 0
  rw [show 1+1+(6*k+5) = 6*k+7 from by ring,
      show 2*k^2+2*k+1+(6*k+5) = 2*k^2+8*k+6 from by ring,
      show 0+(6*k+5) = 6*k+5 from by ring] at h
  convert h using 1

-- Odd->Even: (6k+7, 0, 2k²+8k+6, 0, 0) ⊢⁺ (6k+11, 0, 2k²+10k+11, 0, 0)
theorem odd_to_even (k : ℕ) :
    ⟨6*k+7, 0, 2*k^2+8*k+6, 0, 0⟩ [fm]⊢⁺ ⟨6*k+11, 0, 2*k^2+10*k+11, 0, 0⟩ := by
  -- Phase 1: a → d
  apply stepStar_stepPlus_stepPlus
  · show ⟨6*k+7, 0, 2*k^2+8*k+6, 0, 0⟩ [fm]⊢* ⟨0, 0, 2*k^2+8*k+6, 6*k+7, 0⟩
    have h := a_to_d (6*k+7) 0 (2*k^2+8*k+6) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R5/R1/R1
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 2*k^2+8*k+6, 6*k+7, 0⟩ [fm]⊢* ⟨0, 0, 2*k^2+4*k+2, 1, 6*k+6⟩
    have h := r5r1r1 (2*k+2) (2*k^2+4*k+2) 1 0
    rw [show 2*k^2+4*k+2+2*(2*k+2) = 2*k^2+8*k+6 from by ring,
        show 1+3*(2*k+2) = 6*k+7 from by ring,
        show 0+3*(2*k+2) = 6*k+6 from by ring] at h; exact h
  -- Phase 3: R5+R2+R2
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 2*k^2+4*k+2, 1, 6*k+6⟩ [fm]⊢* ⟨2, 1, 2*k^2+4*k+3, 0, 6*k+7⟩
    apply stepStar_trans (c₂ := ⟨0, 2, 2*k^2+4*k+2, 0, 6*k+7⟩)
    · exact step_stepStar (show fm ⟨0, 0, 2*k^2+4*k+2, 1, 6*k+6⟩ = some ⟨0, 2, 2*k^2+4*k+2, 0, 6*k+7⟩
        from by simp [fm])
    · exact step_stepStar (r2_b2 _ _)
  apply step_stepStar_stepPlus
  · show ⟨2, 1, 2*k^2+4*k+3, 0, 6*k+7⟩ [fm]⊢ ⟨4, 0, 2*k^2+4*k+4, 0, 6*k+7⟩
    exact r2_ab1 _ _ _
  -- Phase 4: R3/R2
  show ⟨4, 0, 2*k^2+4*k+4, 0, 6*k+7⟩ [fm]⊢* ⟨6*k+11, 0, 2*k^2+10*k+11, 0, 0⟩
  have h := r3r2 (6*k+7) 3 (2*k^2+4*k+4) 0
  rw [show 3+1+(6*k+7) = 6*k+11 from by ring,
      show 2*k^2+4*k+4+(6*k+7) = 2*k^2+10*k+11 from by ring,
      show 0+(6*k+7) = 6*k+7 from by ring] at h
  convert h using 1

theorem main_trans (k : ℕ) :
    ⟨6*k+5, 0, 2*k^2+6*k+3, 0, 0⟩ [fm]⊢⁺ ⟨6*(k+1)+5, 0, 2*(k+1)^2+6*(k+1)+3, 0, 0⟩ := by
  rw [show 6*(k+1)+5 = 6*k+11 from by ring,
      show 2*(k+1)^2+6*(k+1)+3 = 2*k^2+10*k+11 from by ring]
  exact stepPlus_trans (even_to_odd k) (odd_to_even k)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨6*0+5, 0, 2*0^2+6*0+3, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨6*k+5, 0, 2*k^2+6*k+3, 0, 0⟩) 0
  intro k
  exact ⟨k+1, main_trans k⟩

end Sz22_2003_unofficial_236
