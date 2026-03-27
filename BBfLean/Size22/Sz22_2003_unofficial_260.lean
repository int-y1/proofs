import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #260: [14/15, 1/3, 33/7, 125/2, 1/55, 3/5]

Vector representation:
```
 1 -1 -1  1  0
 0 -1  0  0  0
 0  1  0 -1  1
-1  0  3  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_260

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Climbing phase: repeated Rule1+Rule3 pairs
-- From (k, 1, n, 0, k), each pair yields (k+1, 1, n-1, 0, k+1)
theorem climb : ∀ n, ∀ k, ⟨k, 1, n, 0, k⟩ [fm]⊢* ⟨k+n, 1, 0, 0, k+n⟩ := by
  intro n; induction' n with n ih <;> intro k
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih (k + 1))
  ring_nf; finish

-- Rule 2: (m, 1, 0, 0, m) → (m, 0, 0, 0, m)
theorem drop_b : ⟨m, 1, 0, 0, m⟩ [fm]⊢ ⟨m, 0, 0, 0, m⟩ := by
  unfold fm; simp

-- Expanding phase: Rule 4 repeated, converting a to c
theorem expand : ∀ a, ∀ c e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * a, 0, e⟩ := by
  intro a; induction' a with a ih <;> intro c e
  · exists 0
  step fm
  apply stepStar_trans (ih (c + 3) e)
  ring_nf; finish

-- Contracting phase: Rule 5 repeated, consuming c and e together
theorem contract : ∀ e, ∀ c, ⟨0, 0, c + e, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro e; induction' e with e ih <;> intro c
  · exists 0
  step fm
  apply stepStar_trans (ih c)
  ring_nf; finish

-- Main transition: (0, 0, C+3, 0, 0) →⁺ (0, 0, 2*C+4, 0, 0) for all C
theorem main_trans (C : ℕ) : ⟨0, 0, C + 3, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * C + 4, 0, 0⟩ := by
  -- Step 1: Rule 6: (0, 0, C+3, 0, 0) → (0, 1, C+2, 0, 0)
  step fm
  -- Step 2: Climbing: (0, 1, C+2, 0, 0) →* (C+2, 1, 0, 0, C+2)
  apply stepStar_trans (climb (C + 2) 0)
  simp only [Nat.zero_add]
  -- Step 3: Drop b: (C+2, 1, 0, 0, C+2) → (C+2, 0, 0, 0, C+2)
  apply stepStar_trans (step_stepStar drop_b)
  -- Step 4: Expanding: (C+2, 0, 0, 0, C+2) →* (0, 0, 3*(C+2), 0, C+2)
  apply stepStar_trans (expand (C + 2) 0 (C + 2))
  simp only [Nat.zero_add]
  -- Step 5: Contracting: (0, 0, 3*(C+2), 0, C+2) →* (0, 0, 2*(C+2), 0, 0)
  -- 3*(C+2) = 2*(C+2) + (C+2)
  rw [show 3 * (C + 2) = 2 * (C + 2) + (C + 2) from by ring]
  apply stepStar_trans (contract (C + 2) (2 * (C + 2)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 3, 0, 0⟩) 0
  intro n; exact ⟨2 * n + 1, by
    show ⟨0, 0, n + 3, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, (2 * n + 1) + 3, 0, 0⟩
    rw [show (2 * n + 1) + 3 = 2 * n + 4 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_260
