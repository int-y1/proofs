import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1527: [7/30, 121/3, 15/77, 4/11, 21/2]

Vector representation:
```
-1 -1 -1  1  0
 0 -1  0  0  2
 0  1  1 -1 -1
 2  0  0  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1527

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3,R2 chain: drains d while a=0, b=0, with e >= 1.
theorem r3r2_chain : ∀ k c e, ⟨0, 0, c, k, e + 1⟩ [fm]⊢* ⟨0, 0, c + k, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e
    rw [show c + (k + 1) = (c + 1) + k from by ring,
        show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm
    exact ih (c + 1) (e + 1)

-- R4 chain: drains e while b=0, d=0, building a.
theorem r4_chain : ∀ k a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih
  · intro a c; exists 0
  · intro a c
    rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    exact ih (a + 2) c

-- R5,R1 chain: drains c and a, building d.
theorem r5r1_chain : ∀ k a d, ⟨a + 2 * k, 0, k, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a d; exists 0
  · intro a d
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 2 from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm
    exact ih a (d + 2)

-- Main transition: (4, 0, 0, d, 0) ⊢⁺ (4, 0, 0, 2*d+4, 0)
theorem main_trans (d : ℕ) :
    ⟨4, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨4, 0, 0, 2 * d + 4, 0⟩ := by
  -- Phase 1: 8 explicit steps: (4,0,0,d,0) -> (0,0,0,d+2,2)
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  -- Phase 2: R3,R2 chain: (0,0,0,d+2,2) -> (0,0,d+2,0,d+4)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r2_chain (d + 2) 0 1)
  rw [show 0 + (d + 2) = d + 2 from by ring,
      show 1 + (d + 2) + 1 = d + 4 from by ring]
  -- Phase 3: R4 chain: (0,0,d+2,0,d+4) -> (2*d+8,0,d+2,0,0)
  apply stepStar_trans (r4_chain (d + 4) 0 (d + 2))
  rw [show 0 + 2 * (d + 4) = 2 * d + 8 from by ring]
  -- Phase 4: R5,R1 chain: (2*d+8,0,d+2,0,0) -> (4,0,0,2*d+4,0)
  rw [show 2 * d + 8 = 4 + 2 * (d + 2) from by ring]
  apply stepStar_trans (r5r1_chain (d + 2) 4 0)
  rw [show 0 + 2 * (d + 2) = 2 * d + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 2, 0⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨4, 0, 0, d, 0⟩) 2
  intro d; exact ⟨2 * d + 4, main_trans d⟩

end Sz22_2003_unofficial_1527
