import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1731: [8/15, 33/14, 275/2, 7/11, 3/5]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1731

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: move e to d (a=0, b=0)
theorem e_to_d : ∀ k d, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R3 chain: convert a to c and e (b=0, d=0)
theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) (e + 1))
    ring_nf; finish

-- R2+R1 spiral
theorem spiral : ∀ k, ∀ a c d e, ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

-- Case 1: F >= 1
theorem case1 {D F : ℕ} : ⟨0, 0, D + F + 3, D + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 4 * D + F + 10, 3 * D + 6, 0⟩ := by
  step fm; step fm
  -- Goal: (3, 0, D + F + 1, D + 1, 0) ⊢* (0, 0, 4D+F+10, 3D+6, 0)
  -- Use spiral (D+1) with a=2, c=F, d=0, e=0
  have hs := spiral (D + 1) 2 F 0 0
  -- hs : (3, 0, F + (D+1), D+1, 0) ⊢* (2D+5, 0, F, 0, D+1)
  -- Rewrite hs to match goal LHS
  rw [show F + (D + 1) = D + F + 1 from by ring,
      show (0 : ℕ) + (D + 1) = D + 1 from by ring,
      show (2 : ℕ) + 1 = 3 from by ring,
      show 2 + 2 * (D + 1) + 1 = 2 * D + 5 from by ring] at hs
  apply stepStar_trans hs
  -- Goal: (2D+5, 0, F, 0, D+1) ⊢* (0, 0, 4D+F+10, 3D+6, 0)
  -- Use r3_chain then e_to_d
  have hr := r3_chain (2 * D + 5) 0 F (D + 1)
  rw [show (0 : ℕ) + (2 * D + 5) = 2 * D + 5 from by ring,
      show F + 2 * (2 * D + 5) = 4 * D + F + 10 from by ring,
      show D + 1 + (2 * D + 5) = 3 * D + 6 from by ring] at hr
  apply stepStar_trans hr
  -- Goal: (0, 0, 4D+F+10, 0, 3D+6) ⊢* (0, 0, 4D+F+10, 3D+6, 0)
  rw [show 3 * D + 6 = 0 + (3 * D + 6) from by ring]
  exact e_to_d (3 * D + 6) 0

-- Case 2: F = 0
theorem case2 {D : ℕ} : ⟨0, 0, D + 2, D + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 4 * D + 9, 3 * D + 6, 0⟩ := by
  step fm; step fm
  -- Goal: (3, 0, D, D+1, 0) ⊢* (0, 0, 4D+9, 3D+6, 0)
  have hs := spiral D 2 0 1 0
  rw [show (0 : ℕ) + D = D from by ring,
      show 1 + D = D + 1 from by ring,
      show (2 : ℕ) + 1 = 3 from by ring,
      show 2 + 2 * D + 1 = 2 * D + 3 from by ring] at hs
  apply stepStar_trans hs
  -- Goal: (2D+3, 0, 0, 1, D) ⊢* (0, 0, 4D+9, 3D+6, 0)
  rw [show 2 * D + 3 = (2 * D + 2) + 1 from by ring]
  step fm  -- R2: (2D+2, 1, 0, 0, D+1)
  rw [show 2 * D + 2 = (2 * D + 1) + 1 from by ring]
  step fm  -- R3: (2D+1, 1, 2, 0, D+2)
  step fm  -- R1: (2D+4, 0, 1, 0, D+2)
  -- (2D+1+3, 0, 1, 0, D+2)
  rw [show 2 * D + 1 + 3 = 2 * D + 4 from by ring]
  -- Goal: (2D+4, 0, 1, 0, D+2) ⊢* (0, 0, 4D+9, 3D+6, 0)
  have hr := r3_chain (2 * D + 4) 0 1 (D + 2)
  rw [show (0 : ℕ) + (2 * D + 4) = 2 * D + 4 from by ring,
      show 1 + 2 * (2 * D + 4) = 4 * D + 9 from by ring,
      show D + 2 + (2 * D + 4) = 3 * D + 6 from by ring] at hr
  apply stepStar_trans hr
  -- Goal: (0, 0, 4D+9, 0, 3D+6) ⊢* (0, 0, 4D+9, 3D+6, 0)
  rw [show 3 * D + 6 = 0 + (3 * D + 6) from by ring]
  exact e_to_d (3 * D + 6) 0

-- Main transition
theorem main_trans (F D : ℕ) : ⟨0, 0, D + F + 2, D + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 4 * D + F + 9, 3 * D + 6, 0⟩ := by
  rcases F with _ | F'
  · rw [show D + 0 + 2 = D + 2 from by ring,
        show 4 * D + 0 + 9 = 4 * D + 9 from by ring]
    exact case2
  · rw [show D + (F' + 1) + 2 = D + F' + 3 from by ring,
        show 4 * D + (F' + 1) + 9 = 4 * D + F' + 10 from by ring]
    exact case1

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0 + 0 + 2, 0 + 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, D⟩ ↦ ⟨0, 0, D + F + 2, D + 1, 0⟩) ⟨0, 0⟩
  intro ⟨F, D⟩
  refine ⟨⟨D + F + 2, 3 * D + 5⟩, ?_⟩
  show ⟨0, 0, D + F + 2, D + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, (3 * D + 5) + (D + F + 2) + 2, (3 * D + 5) + 1, 0⟩
  rw [show (3 * D + 5) + (D + F + 2) + 2 = 4 * D + F + 9 from by ring,
      show (3 * D + 5) + 1 = 3 * D + 6 from by ring]
  exact main_trans F D
