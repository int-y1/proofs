import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #215: [1/9, 175/3, 3/55, 2/5, 11/14, 3/2]

Vector representation:
```
 0 -2  0  0  0
 0 -1  2  1  0
 0  1 -1  0 -1
 1  0 -1  0  0
-1  0  0 -1  1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_215

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3/R2 pairs: consume e while building c and d
theorem r3r2_pairs : ∀ k c d, ⟨0, 0, c + 2, d + 1, k⟩ [fm]⊢* ⟨0, 0, c + k + 2, d + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show c + (k + 1) + 2 = (c + 1) + k + 2 from by ring,
      show d + (k + 1) + 1 = (d + 1) + k + 1 from by ring]
  step fm
  step fm
  exact ih (c + 1) (d + 1)

-- R4 chain: (a, 0, k+1, d, 0) →* (a+k+1, 0, 0, d, 0)
theorem r4_chain : ∀ k a d, ⟨a, 0, k + 1, d, 0⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · step fm; finish
  rw [show (k + 1) + 1 = k + 1 + 1 from rfl]
  step fm
  apply stepStar_trans (ih (a + 1) d)
  ring_nf; finish

-- R5 chain: (k+1, 0, 0, k, e) →* (1, 0, 0, 0, e+k)
theorem r5_chain : ∀ k e, ⟨k + 1, 0, 0, k, e⟩ [fm]⊢* ⟨1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  step fm
  apply stepStar_trans (ih (e + 1))
  ring_nf; finish

-- Main cycle: (0, 1, 0, 0, e) ⊢⁺ (0, 1, 0, 0, e + 1)
theorem main_cycle (e : ℕ) : ⟨0, 1, 0, 0, e⟩ [fm]⊢⁺ ⟨0, 1, 0, 0, e + 1⟩ := by
  -- R2: (0, 1, 0, 0, e) → (0, 0, 2, 1, e)
  -- R3/R2 pairs: (0, 0, 2, 1, e) →* (0, 0, e+2, e+1, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, e + 2, e + 1, 0⟩)
  · step fm
    have h := r3r2_pairs e 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- R4 chain: (0, 0, e+2, e+1, 0) →* (e+2, 0, 0, e+1, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨e + 2, 0, 0, e + 1, 0⟩)
  · rw [show e + 2 = (e + 1) + 1 from by ring]
    have h := r4_chain (e + 1) 0 (e + 1)
    simp only [Nat.zero_add] at h
    exact h
  -- R5 chain: (e+2, 0, 0, e+1, 0) →* (1, 0, 0, 0, e+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 0, 0, 0, e + 1⟩)
  · rw [show e + 2 = (e + 1) + 1 from by ring]
    have h := r5_chain (e + 1) 0
    simp only [Nat.zero_add] at h
    exact h
  -- R6: (1, 0, 0, 0, e+1) → (0, 1, 0, 0, e+1)
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun e ↦ ⟨0, 1, 0, 0, e⟩) 0
  intro e
  exact ⟨e + 1, main_cycle e⟩

end Sz22_2003_unofficial_215
