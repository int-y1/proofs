import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1598: [77/15, 13/3, 18/91, 5/11, 45/2]

Vector representation:
```
 0 -1 -1  1  1  0
 0 -1  0  0  0  1
 1  2  0 -1  0 -1
 0  0  1  0 -1  0
-1  2  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1598

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c+1, d, e, f⟩
  | _ => none

-- R4 chain: transfer e to c.
theorem e_to_c : ∀ k, ∀ a c f, ⟨a, 0, c, 0, k, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a c f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (c + 1) f); ring_nf; finish

-- R3+R2+R2 drain: (a, 0, 0, d+1, e, f+1) →* (a+d+1, 0, 0, 0, e, f+d+2).
theorem drain : ∀ k, ∀ a e f, ⟨a, 0, 0, k, e, f + 1⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e, f + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) e (f + 1)); ring_nf; finish

-- Combined spiral + drain by strong induction on c.
-- From (a, 0, c, d+1, e, f+c+1) to (a+c+d+1, 0, 0, 0, e+c, f+c+d+2).
theorem spiral_drain : ∀ C, ∀ A D E F,
    ⟨A, 0, C, D + 1, E, F + C + 1⟩ [fm]⊢* ⟨A + C + D + 1, 0, 0, 0, E + C, F + C + D + 2⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih
  rcases C with _ | _ | C
  · -- C = 0: just drain.
    intro A D E F
    exact drain (D + 1) A E F
  · -- C = 1: R3 + R1 + R2, then drain.
    intro A D E F
    step fm; step fm; step fm
    apply stepStar_trans (drain (D + 1) (A + 1) (E + 1) (F + 1))
    ring_nf; finish
  · -- C + 2: one full round (R3 + R1 + R1), then recurse on C.
    intro A D E F
    rw [show C + 2 = C + 1 + 1 from by ring,
        show F + (C + 2) + 1 = F + C + 2 + 1 from by ring]
    step fm; step fm; step fm
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring,
        show F + C + 2 = (F + 1) + C + 1 from by ring]
    apply stepStar_trans (ih C (by omega) (A + 1) (D + 1) (E + 2) (F + 1))
    ring_nf; finish

-- Main transition: (a+2, 0, 0, 0, e+2, 2*e+4) ⊢⁺ (a+e+4, 0, 0, 0, e+3, 2*e+6).
theorem main_trans (a e : ℕ) :
    ⟨a + 2, 0, 0, 0, e + 2, 2 * e + 4⟩ [fm]⊢⁺ ⟨a + e + 4, 0, 0, 0, e + 3, 2 * e + 6⟩ := by
  -- Phase 1: R4 transfer e+2 to c.
  have phase1 : ⟨a + 2, 0, 0, 0, e + 2, 2 * e + 4⟩ [fm]⊢* ⟨a + 2, 0, e + 2, 0, 0, 2 * e + 4⟩ := by
    have := e_to_c (e + 2) (a + 2) 0 (2 * e + 4)
    simp at this; exact this
  -- Phase 2: R5 step.
  have phase2 : ⟨a + 2, 0, e + 2, 0, 0, 2 * e + 4⟩ [fm]⊢⁺ ⟨a + 1, 2, e + 3, 0, 0, 2 * e + 4⟩ := by
    rw [show a + 2 = (a + 1) + 1 from by ring]
    step fm; finish
  -- Phase 3: R1 + R1.
  have phase3 : ⟨a + 1, 2, e + 3, 0, 0, 2 * e + 4⟩ [fm]⊢* ⟨a + 1, 0, e + 1, 2, 2, 2 * e + 4⟩ := by
    rw [show e + 3 = (e + 1) + 1 + 1 from by ring]
    step fm; step fm; finish
  -- Phase 4: spiral + drain.
  have phase4 : ⟨a + 1, 0, e + 1, 2, 2, 2 * e + 4⟩ [fm]⊢* ⟨a + e + 4, 0, 0, 0, e + 3, 2 * e + 6⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show 2 * e + 4 = (e + 2) + (e + 1) + 1 from by ring]
    apply stepStar_trans (spiral_drain (e + 1) (a + 1) 1 2 (e + 2))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus phase1
    (stepPlus_stepStar_stepPlus phase2
      (stepStar_trans phase3 phase4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2, 4⟩)
  · execute fm 16
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 2, 0, 0, 0, e + 2, 2 * e + 4⟩) ⟨0, 0⟩
  intro ⟨a, e⟩; exact ⟨⟨a + e + 2, e + 1⟩, main_trans a e⟩

end Sz22_2003_unofficial_1598
