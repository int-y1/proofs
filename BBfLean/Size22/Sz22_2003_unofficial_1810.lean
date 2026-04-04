import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1810: [9/10, 55/21, 2/3, 7/11, 315/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  2  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1810

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d+1, e⟩
  | _ => none

-- R4 chain: move e to d
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (d + 1))
    rw [show d + 1 + k = d + (k + 1) from by ring]; finish

-- R3 chain: move b to a
theorem b_to_a : ∀ k a, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a + 1))
    rw [show a + 1 + k = a + (k + 1) from by ring]; finish

-- R2+R1 chain
theorem r2r1_chain : ∀ k a b d e, ⟨a + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + 1 + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    rw [show (b + 1) + 1 + k = b + 1 + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; finish

-- R5+R1: (a+2, 0, 0, d+1, 0) →⁺ (a, 4, 0, d+2, 0)
theorem r5_r1 : ⟨a + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨a, 4, 0, d + 2, 0⟩ := by
  step fm; step fm; finish

-- Full macro step
theorem macro_step (n : ℕ) : ⟨2 * n + 5, 0, 0, 0, n + 2⟩ [fm]⊢⁺ ⟨2 * n + 7, 0, 0, 0, n + 3⟩ := by
  -- Phase 1: e_to_d
  apply stepStar_stepPlus_stepPlus
  · have h := e_to_d (n + 2) 0 (a := 2 * n + 5) (e := 0)
    simp at h; exact h
  -- Phase 2: R5+R1
  apply stepPlus_stepStar_stepPlus
  · have h := @r5_r1 (2 * n + 3) (n + 1)
    rw [show (2 * n + 3) + 2 = 2 * n + 5 from by ring,
        show (n + 1) + 1 = n + 2 from by ring,
        show (n + 1) + 2 = n + 3 from by ring] at h
    exact h
  -- Phase 3: R2R1 chain
  apply stepStar_trans
  · have h := r2r1_chain (n + 3) n 3 0 0
    rw [show n + (n + 3) = 2 * n + 3 from by ring,
        show (3 : ℕ) + 1 = 4 from by ring,
        show (0 : ℕ) + (n + 3) = n + 3 from by ring,
        show 4 + (n + 3) = n + 7 from by ring] at h
    exact h
  -- Phase 4: R3 chain
  have h := b_to_a (n + 7) n (b := 0) (e := n + 3)
  rw [show (0 : ℕ) + (n + 7) = n + 7 from by ring,
      show n + (n + 7) = 2 * n + 7 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 2⟩) (by execute fm 22)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 5, 0, 0, 0, n + 2⟩) 0
  intro n; exists n + 1; exact macro_step n
