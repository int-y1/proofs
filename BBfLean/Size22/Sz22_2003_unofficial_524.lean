import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #524: [28/15, 33/2, 1/3, 25/11, 1/35, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0  1
 0 -1  0  0  0
 0  0  2  0 -1
 0  0 -1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_524

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1R2 interleaved chain: consumes c via alternating R1,R2
theorem r1r2_chain : ∀ k, ∀ a d e, ⟨a, 1, k+1, d, e⟩ [fm]⊢* ⟨a+k+2, 0, 0, d+k+1, e+k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · step fm; finish
  rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2 repeated: drain a into b and e (requires c=0)
theorem a_to_be : ∀ k, ∀ a b d e, ⟨a+k, b, 0, d, e⟩ [fm]⊢* ⟨a, b+k, 0, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R3 repeated: drain b (requires a=0, c=0)
theorem b_drain : ∀ k, ∀ b d e, ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: convert e to c (requires a=0, b=0)
theorem e_to_c : ∀ k, ∀ c d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R5 repeated: annihilate c and d
theorem cd_drain : ∀ k, ∀ c d, ⟨0, 0, c+k, d+k, 0⟩ [fm]⊢* ⟨0, 0, c, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega,
      show d + (k + 1) = (d + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- All phases after R6 combined as ⊢*
theorem phases_star (c : ℕ) : ⟨0, 1, c+1, 0, 0⟩ [fm]⊢* ⟨0, 0, 3*c+3, 0, 0⟩ := by
  -- R1R2 chain: (0, 1, c+1, 0, 0) →* (c+2, 0, 0, c+1, c)
  have h1 : ⟨(0 : ℕ), 1, c+1, 0, 0⟩ [fm]⊢* ⟨c+2, 0, 0, c+1, c⟩ := by
    have := r1r2_chain c 0 0 0; ring_nf at this ⊢; exact this
  -- R2 drain: (c+2, 0, 0, c+1, c) →* (0, c+2, 0, c+1, 2*c+2)
  have h2 : ⟨c+2, 0, 0, c+1, c⟩ [fm]⊢* ⟨0, c+2, 0, c+1, 2*c+2⟩ := by
    have := a_to_be (c+2) 0 0 (c+1) c; ring_nf at this ⊢; exact this
  -- R3 drain: (0, c+2, 0, c+1, 2*c+2) →* (0, 0, 0, c+1, 2*c+2)
  have h3 : ⟨(0 : ℕ), c+2, 0, c+1, 2*c+2⟩ [fm]⊢* ⟨0, 0, 0, c+1, 2*c+2⟩ := by
    have := b_drain (c+2) 0 (c+1) (2*c+2); ring_nf at this ⊢; exact this
  -- R4 chain: (0, 0, 0, c+1, 2*c+2) →* (0, 0, 4*c+4, c+1, 0)
  have h4 : ⟨(0 : ℕ), 0, 0, c+1, 2*c+2⟩ [fm]⊢* ⟨0, 0, 4*c+4, c+1, 0⟩ := by
    have := e_to_c (2*c+2) 0 (c+1) 0; ring_nf at this ⊢; exact this
  -- R5 chain: (0, 0, 4*c+4, c+1, 0) →* (0, 0, 3*c+3, 0, 0)
  have h5 : ⟨(0 : ℕ), 0, 4*c+4, c+1, 0⟩ [fm]⊢* ⟨0, 0, 3*c+3, 0, 0⟩ := by
    have := cd_drain (c+1) (3*c+3) 0; ring_nf at this ⊢; exact this
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

-- Main transition: (0, 0, c+2, 0, 0) →⁺ (0, 0, 3*c+3, 0, 0)
theorem main_trans (c : ℕ) : ⟨0, 0, c+2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3*c+3, 0, 0⟩ := by
  -- R6: (0, 0, c+2, 0, 0) → (0, 1, c+1, 0, 0)
  apply stepPlus_stepStar_stepPlus
  · step fm; finish
  exact phases_star c

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun c ↦ ⟨0, 0, c+2, 0, 0⟩) 0
  intro c; exists 3*c+1
  exact main_trans c

end Sz22_2003_unofficial_524
