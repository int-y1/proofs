import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1777: [9/10, 343/2, 22/21, 5/11, 22/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  3  0
 1 -1  0 -1  1
 0  0  1  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1777

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 chain: move e to c.
theorem e_to_c : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R1+R3 chain: each round does R1 then R3.
theorem r1r3_chain : ∀ k b c d e, ⟨1, b, c + k, d + k, e⟩ [fm]⊢* ⟨1, b + k, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) c d (e + 1))
    ring_nf; finish

-- R2+R3 chain: each round does R2 then R3.
theorem r2r3_chain : ∀ k b d e, ⟨1, b + k, 0, d, e⟩ [fm]⊢* ⟨1, b, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    rw [show (b + k + 1 : ℕ) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (d + 2) (e + 1))
    ring_nf; finish

-- Full transition: (0, 0, c, c+F+2, 0) ⊢⁺ (0, 0, 2c+1, 2c+F+4, 0)
-- Phases: R5 -> c*(R1,R3) -> c*(R2,R3) -> R2 -> (2c+1)*R4
theorem main_trans (c F : ℕ) : ⟨0, 0, c, c + F + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 1, F + 2 * c + 4, 0⟩ := by
  -- R5 step: (0,0,c,(c+F+1)+1,0) -> (1,0,c,c+F+1,1)
  have h1 : ⟨0, 0, c, c + F + 2, 0⟩ [fm]⊢ ⟨1, 0, c, c + F + 1, 1⟩ := by
    rw [show c + F + 2 = (c + F + 1) + 1 from by ring]; simp [fm]
  -- R1/R3 chain: (1, 0, 0+c, (F+1)+c, 1) ->* (1, 0+c, 0, F+1, 1+c)
  have h2 : ⟨1, 0, c, c + F + 1, 1⟩ [fm]⊢* ⟨1, c, 0, F + 1, c + 1⟩ := by
    have := r1r3_chain c 0 0 (F + 1) 1
    simp only [Nat.zero_add] at this
    rwa [show F + 1 + c = c + F + 1 from by ring, show 1 + c = c + 1 from by ring] at this
  -- R2/R3 chain: (1, 0+c, 0, F+1, c+1) ->* (1, 0, 0, F+1+2c, c+1+c)
  have h3 : ⟨1, c, 0, F + 1, c + 1⟩ [fm]⊢* ⟨1, 0, 0, F + 1 + 2 * c, 2 * c + 1⟩ := by
    have := r2r3_chain c 0 (F + 1) (c + 1)
    simp only [Nat.zero_add] at this
    rwa [show c + 1 + c = 2 * c + 1 from by ring] at this
  -- Final R2: (1, 0, 0, F+1+2c, 2c+1) -> (0, 0, 0, F+2c+4, 2c+1)
  have h4 : ⟨1, 0, 0, F + 1 + 2 * c, 2 * c + 1⟩ [fm]⊢ ⟨0, 0, 0, F + 2 * c + 4, 2 * c + 1⟩ := by
    rw [show F + 1 + 2 * c = (F + 2 * c + 1) from by ring]; simp [fm]
  -- e_to_c: (0, 0, 0, F+2c+4, 0+(2c+1)) ->* (0, 0, 0+(2c+1), F+2c+4, 0)
  have h5 : ⟨0, 0, 0, F + 2 * c + 4, 2 * c + 1⟩ [fm]⊢* ⟨0, 0, 2 * c + 1, F + 2 * c + 4, 0⟩ := by
    have := e_to_c (2 * c + 1) 0 (F + 2 * c + 4) 0
    simp only [Nat.zero_add] at this
    exact this
  exact step_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans (step_stepStar h4) h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 5, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, F⟩ ↦ ⟨0, 0, c, c + F + 2, 0⟩) ⟨1, 2⟩
  intro ⟨c, F⟩
  refine ⟨⟨2 * c + 1, F + 1⟩, ?_⟩
  show ⟨0, 0, c, c + F + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 1, (2 * c + 1) + (F + 1) + 2, 0⟩
  rw [show (2 * c + 1) + (F + 1) + 2 = F + 2 * c + 4 from by ring]
  exact main_trans c F
