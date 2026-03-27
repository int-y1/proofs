import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #218: [1/90, 9/77, 14/3, 5/7, 363/2]

Vector representation:
```
-1 -2 -1  0  0
 0  2  0 -1 -1
 1 -1  0  1  0
 0  0  1 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_218

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- Phase 1: R3/R2 pairs while c=0, d=0.
-- (a, b+1, 0, 0, k) →* (a+k, b+k+1, 0, 0, 0)
theorem r3r2_pairs : ∀ k a b, ⟨a, b + 1, 0, 0, k⟩ [fm]⊢* ⟨a + k, b + k + 1, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + 1) + k from by ring,
      show b + (k + 1) + 1 = (b + 1) + k + 1 from by ring]
  step fm
  step fm
  exact ih (a + 1) (b + 1)

-- Phase 2: R3 chain with e=0, c=0.
-- (a, k, 0, d, 0) →* (a+k, 0, 0, d+k, 0)
theorem r3_chain : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show a + (k + 1) = (a + 1) + k from by ring,
      show d + (k + 1) = (d + 1) + k from by ring]
  step fm
  exact ih (a + 1) (d + 1)

-- Phase 3: R4 chain.
-- (a, 0, c, k, 0) →* (a, 0, c+k, 0, 0)
theorem r4_chain : ∀ k a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show c + (k + 1) = (c + 1) + k from by ring]
  step fm
  exact ih a (c + 1)

-- Phase 4: 4-step cycle R5/R3/R2/R1.
-- (a + k + 1, 0, k, 0, e) →* (a + 1, 0, 0, 0, e + k)
theorem r5r3r2r1_loop : ∀ k a e, ⟨a + k + 1, 0, k, 0, e⟩ [fm]⊢* ⟨a + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + (k + 1) + 1 = a + k + 2 from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  step fm
  step fm
  step fm
  step fm
  exact ih a (e + 1)

-- Main cycle: (a + 1, 0, 0, 0, e) ⊢⁺ (a + e + 2, 0, 0, 0, e + 3)
theorem main_cycle (a e : ℕ) : ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a + e + 2, 0, 0, 0, e + 3⟩ := by
  -- R5: (a+1, 0, 0, 0, e) → (a, 1, 0, 0, e+2)
  step fm
  -- Now goal: (a, 1, 0, 0, e+2) [fm]⊢* (a+e+2, 0, 0, 0, e+3)
  -- Phase 1: R3/R2 pairs
  apply stepStar_trans (c₂ := ⟨a + e + 2, e + 3, 0, 0, 0⟩)
  · have h := r3r2_pairs (e + 2) a 0
    rw [show a + (e + 2) = a + e + 2 from by ring,
        show 0 + (e + 2) + 1 = e + 3 from by ring] at h
    exact h
  -- Phase 2: R3 chain
  apply stepStar_trans (c₂ := ⟨a + 2 * e + 5, 0, 0, e + 3, 0⟩)
  · have h := r3_chain (e + 3) (a + e + 2) 0
    rw [show a + e + 2 + (e + 3) = a + 2 * e + 5 from by ring] at h
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 3: R4 chain
  apply stepStar_trans (c₂ := ⟨a + 2 * e + 5, 0, e + 3, 0, 0⟩)
  · have h := r4_chain (e + 3) (a + 2 * e + 5) 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 4: R5/R3/R2/R1 loop
  have h := r5r3r2r1_loop (e + 3) (a + e + 1) 0
  rw [show a + e + 1 + (e + 3) + 1 = a + 2 * e + 5 from by ring,
      show a + e + 1 + 1 = a + e + 2 from by ring,
      show 0 + (e + 3) = e + 3 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 23)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ) (fun ⟨a, e⟩ ↦ ⟨a + 1, 0, 0, 0, e⟩) ⟨1, 3⟩
  intro ⟨a, e⟩
  exact ⟨⟨a + e + 1, e + 3⟩, by
    show ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨(a + e + 1) + 1, 0, 0, 0, e + 3⟩
    rw [show (a + e + 1) + 1 = a + e + 2 from by ring]
    exact main_cycle a e⟩

end Sz22_2003_unofficial_218
