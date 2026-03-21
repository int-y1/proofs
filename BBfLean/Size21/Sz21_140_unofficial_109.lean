import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #109: [7/45, 242/5, 5/77, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
 1  0 -1  0  2
 0  0  1 -1 -1
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_109

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R3/R2 drain d when b=0: each pair R3 then R2
theorem drain_d_b0 : ∀ k, ∀ a e, ⟨a, 0, 0, k, e + 1⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  -- (a, 0, 0, k+1, e+1): R3 fires (d=k+1 >= 1, e+1 >= 1)
  step fm
  -- (a, 0, 1, k, e): R2 fires (c=1)
  step fm
  -- (a+1, 0, 0, k, e+2) = (a+1, 0, 0, k, (e+1)+1)
  apply stepStar_trans (ih (a + 1) (e + 1))
  ring_nf; finish

-- R3/R2 drain d when b=1: each pair R3 then R2
theorem drain_d_b1 : ∀ k, ∀ a e, ⟨a, 1, 0, k, e + 1⟩ [fm]⊢* ⟨a + k, 1, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  -- (a, 1, 0, k+1, e+1): R1 needs b >= 2, b=1 fails. R2 needs c >= 1, c=0 fails.
  -- R3 fires (d=k+1 >= 1, e+1 >= 1)
  step fm
  -- (a, 1, 1, k, e): R1 needs b >= 2, b=1 fails. R2 fires (c=1)
  step fm
  -- (a+1, 1, 0, k, e+2) = (a+1, 1, 0, k, (e+1)+1)
  apply stepStar_trans (ih (a + 1) (e + 1))
  ring_nf; finish

-- R4 repeated: e → b
theorem e_to_b : ∀ k, ∀ a b, ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show b + (k + 1) = (b + 1) + k from by ring]
  step fm
  exact ih a (b + 1)

-- R5/R1 pairs: each pair consumes 1 from a, 2 from b, adds 2 to d
theorem r5r1_pairs : ∀ k, ∀ a b d, ⟨a + k, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
  -- R5 fires: a+k+1 >= 1, and b+2k+2 >= 2 but c=0 so R1 doesn't fire
  step fm
  -- (a+k, b+2k+2, 1, d+1, 0): b+2k+2 >= 2 and c=1 so R1 fires
  rw [show b + 2 * k + 2 = (b + 2 * k) + 2 from by ring]
  step fm
  -- (a+k, b+2k, 0, d+2, 0)
  apply stepStar_trans (ih a b (d + 2))
  ring_nf; finish

-- Main transition: (A+1, 0, 0, 2*D, 0) →⁺ (A+2*D+1, 0, 0, 2*D+6, 0)
-- = (A+2*D+1, 0, 0, 2*(D+3), 0)
theorem main_trans (A D : ℕ) : ⟨A + 1, 0, 0, 2 * D, 0⟩ [fm]⊢⁺ ⟨A + 2 * D + 1, 0, 0, 2 * (D + 3), 0⟩ := by
  -- Phase 1: R5 then R2 then drain_d_b0
  -- R5: (A+1, 0, 0, 2D, 0) → (A, 0, 1, 2D+1, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨A, 0, 1, 2 * D + 1, 0⟩)
  · show fm ⟨A + 1, 0, 0, 2 * D, 0⟩ = some ⟨A, 0, 1, 2 * D + 1, 0⟩
    simp [fm]
  -- R2: (A, 0, 1, 2D+1, 0) → (A+1, 0, 0, 2D+1, 2)
  apply stepStar_trans (c₂ := ⟨A + 1, 0, 0, 2 * D + 1, 2⟩)
  · step fm; finish
  -- drain_d_b0 with k = 2D+1, e = 1: (A+1, 0, 0, 2D+1, 1+1) →* (A+2D+2, 0, 0, 0, 2D+3)
  apply stepStar_trans (c₂ := ⟨A + 2 * D + 2, 0, 0, 0, 2 * D + 3⟩)
  · have h := drain_d_b0 (2 * D + 1) (A + 1) 1
    rw [show A + 1 + (2 * D + 1) = A + 2 * D + 2 from by ring,
        show 1 + (2 * D + 1) + 1 = 2 * D + 3 from by ring] at h
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    exact h
  -- Phase 2: e_to_b: (A+2D+2, 0, 0, 0, 2D+3) → (A+2D+2, 2D+3, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨A + 2 * D + 2, 2 * D + 3, 0, 0, 0⟩)
  · have h := e_to_b (2 * D + 3) (A + 2 * D + 2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5/R1 pairs, D+1 pairs
  -- (A+2D+2, 2D+3, 0, 0, 0) = ((A+D+1)+(D+1), 1+2*(D+1), 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨A + D + 1, 1, 0, 2 * D + 2, 0⟩)
  · rw [show A + 2 * D + 2 = (A + D + 1) + (D + 1) from by ring,
        show 2 * D + 3 = 1 + 2 * (D + 1) from by ring,
        show 2 * D + 2 = 0 + 2 * (D + 1) from by ring]
    exact r5r1_pairs (D + 1) (A + D + 1) 1 0
  -- Phase 4: R5 then R2 then drain_d_b1
  -- R5: (A+D+1, 1, 0, 2D+2, 0) → (A+D, 1, 1, 2D+3, 0)
  apply stepStar_trans (c₂ := ⟨A + D, 1, 1, 2 * D + 3, 0⟩)
  · have : ⟨(A + D) + 1, 1, 0, 2 * D + 2, 0⟩ [fm]⊢ ⟨A + D, 1, 1, 2 * D + 3, 0⟩ := by
      show fm ⟨(A + D) + 1, 1, 0, 2 * D + 2, 0⟩ = some ⟨A + D, 1, 1, 2 * D + 3, 0⟩
      simp [fm]
    rw [show A + D + 1 = (A + D) + 1 from by ring]
    exact step_stepStar this
  -- R2: (A+D, 1, 1, 2D+3, 0) → (A+D+1, 1, 0, 2D+3, 2)
  -- R1 needs b >= 2: b=1 fails. R2 fires (c=1)
  apply stepStar_trans (c₂ := ⟨A + D + 1, 1, 0, 2 * D + 3, 2⟩)
  · step fm; finish
  -- drain_d_b1 with k = 2D+3, e = 1: (A+D+1, 1, 0, 2D+3, 1+1) →* (A+3D+4, 1, 0, 0, 2D+5)
  apply stepStar_trans (c₂ := ⟨A + 3 * D + 4, 1, 0, 0, 2 * D + 5⟩)
  · have h := drain_d_b1 (2 * D + 3) (A + D + 1) 1
    rw [show A + D + 1 + (2 * D + 3) = A + 3 * D + 4 from by ring,
        show 1 + (2 * D + 3) + 1 = 2 * D + 5 from by ring] at h
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    exact h
  -- Phase 5: e_to_b: (A+3D+4, 1, 0, 0, 2D+5) → (A+3D+4, 2D+6, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨A + 3 * D + 4, 2 * D + 6, 0, 0, 0⟩)
  · have h := e_to_b (2 * D + 5) (A + 3 * D + 4) 1
    simp only [show 1 + (2 * D + 5) = 2 * D + 6 from by ring] at h
    exact h
  -- Phase 6: R5/R1 pairs, D+3 pairs
  -- (A+3D+4, 2D+6, 0, 0, 0) = ((A+2D+1)+(D+3), 0+2*(D+3), 0, 0, 0)
  rw [show A + 3 * D + 4 = (A + 2 * D + 1) + (D + 3) from by ring,
      show 2 * D + 6 = 0 + 2 * (D + 3) from by ring]
  have h := r5r1_pairs (D + 3) (A + 2 * D + 1) 0 0
  simp only [Nat.zero_add] at h ⊢; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 6, 0⟩) (by execute fm 28)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, D⟩ ↦ ⟨A + 1, 0, 0, 2 * D, 0⟩) ⟨0, 3⟩
  intro ⟨A, D⟩
  refine ⟨⟨A + 2 * D, D + 3⟩, ?_⟩
  show ⟨A + 1, 0, 0, 2 * D, 0⟩ [fm]⊢⁺ ⟨A + 2 * D + 1, 0, 0, 2 * (D + 3), 0⟩
  exact main_trans A D

end Sz21_140_unofficial_109
