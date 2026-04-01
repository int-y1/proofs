import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1558: [7/45, 121/3, 15/77, 2/11, 63/2]

Vector representation:
```
 0 -2 -1  1  0
 0 -1  0  0  2
 0  1  1 -1 -1
 1  0  0  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1558

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R5+R1 chain: (a+k+1, 0, c+k, d, 0) ⊢* (a+1, 0, c, d+2*k, 0)
theorem r5r1_chain : ∀ k a c d,
    ⟨a + k + 1, 0, c + k, d, 0⟩ [fm]⊢* ⟨a + 1, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- R3+R2 chain: (a, 0, c, d+k, e+1) ⊢* (a, 0, c+k, d, e+k+1)
theorem r3r2_chain : ∀ k a c d e,
    ⟨a, 0, c, d + k, e + 1⟩ [fm]⊢* ⟨a, 0, c + k, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (c + 1) d (e + 1)); ring_nf; finish

-- R4 chain: (a, 0, c, 0, e+k) ⊢* (a+k, 0, c, 0, e)
theorem r4_chain : ∀ k a c e,
    ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c e); ring_nf; finish

-- Main transition
theorem main_trans (a c : ℕ) :
    ⟨a + c + 2, 0, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * c + 7, 0, 2 * c + 3, 0, 0⟩ := by
  -- Phase 1: R5+R1 chain c+1 times then R5+R2+R2
  have phase1 : ⟨a + c + 2, 0, c + 1, 0, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, 2 * c + 2, 0⟩ := by
    have := r5r1_chain (c + 1) a 0 0
    rw [show a + (c + 1) + 1 = a + c + 2 from by ring,
        show 0 + (c + 1) = c + 1 from by ring,
        show 0 + 2 * (c + 1) = 2 * c + 2 from by ring] at this
    exact this
  apply stepStar_stepPlus_stepPlus phase1
  -- R5+R2+R2
  rw [show 2 * c + 2 = 2 * c + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show 2 * c + 1 + 1 + 1 = 2 * c + 3 from by ring]
  -- Now at (a, 0, 0, 2*c+3, 4)
  -- Phase 2: R3+R2 chain
  have phase2 : ⟨a, 0, 0, 2 * c + 3, 4⟩ [fm]⊢* ⟨a, 0, 2 * c + 3, 0, 2 * c + 7⟩ := by
    have := r3r2_chain (2 * c + 3) a 0 0 3
    rw [show 0 + (2 * c + 3) = 2 * c + 3 from by ring,
        show 3 + (2 * c + 3) + 1 = 2 * c + 7 from by ring,
        show (3 + 1 : ℕ) = 4 from by ring] at this
    exact this
  apply stepStar_trans phase2
  -- Phase 3: R4 chain
  have phase3 : ⟨a, 0, 2 * c + 3, 0, 2 * c + 7⟩ [fm]⊢* ⟨a + 2 * c + 7, 0, 2 * c + 3, 0, 0⟩ := by
    have := r4_chain (2 * c + 7) a (2 * c + 3) 0
    rw [show 0 + (2 * c + 7) = 2 * c + 7 from by ring,
        show a + (2 * c + 7) = a + 2 * c + 7 from by ring] at this
    exact this
  exact phase3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 1, 0, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, c⟩ ↦ ⟨a + c + 2, 0, c + 1, 0, 0⟩) ⟨3, 0⟩
  intro ⟨a, c⟩
  refine ⟨⟨a + 3, 2 * c + 2⟩, ?_⟩
  show ⟨a + c + 2, 0, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨(a + 3) + (2 * c + 2) + 2, 0, (2 * c + 2) + 1, 0, 0⟩
  rw [show (a + 3) + (2 * c + 2) + 2 = a + 2 * c + 7 from by ring,
      show (2 * c + 2) + 1 = 2 * c + 3 from by ring]
  exact main_trans a c

end Sz22_2003_unofficial_1558
