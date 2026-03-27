import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #403: [225/14, 7/33, 4/3, 11/5, 15/2]

Vector representation:
```
-1  2  2 -1  0
 0 -1  0  1 -1
 2 -1  0  0  0
 0  0 -1  0  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_403

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c+2, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- Rule 4 repeated: drain c to e (with b=0, d=0)
theorem c_to_e : ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  have many_step : ∀ k e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
    intro k; induction' k with k ih <;> intro e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish
  exact many_step k e

-- Rule 3 repeated: drain b to a (with d=0, e=0)
theorem b_to_a : ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, 0⟩ := by
  have many_step : ∀ k a, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, 0⟩ := by
    intro k; induction' k with k ih <;> intro a
    · exists 0
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish
  exact many_step k a

-- Zigzag: repeated (rule 2, rule 1) pairs
-- (a+k, 1, 1, 0, a+k) ⊢* (a, k+1, 2*k+1, 0, a)
theorem zigzag : ∀ k a, ⟨a + k, 1, 1, 0, a + k⟩ [fm]⊢* ⟨a, k + 1, 2 * k + 1, 0, a⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  rw [show a + (k + 1) = (a + 1) + k from by ring]
  apply stepStar_trans (ih (a + 1))
  step fm
  step fm
  ring_nf; finish

-- Tail of the cycle after zigzag: rule 2, rule 1, then b_to_a
theorem tail : ⟨1, n + 1, 2 * n + 1, 0, 1⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 2 * n + 3, 0, 0⟩ := by
  -- Rule 2 (b=n+1≥1, e=1≥1): -> (1, n, 2*n+1, 1, 0)
  step fm
  -- Rule 1 (a=1≥1, d=1≥1): -> (0, n+2, 2*n+3, 0, 0)
  step fm
  -- b_to_a: (0, n+2, 2*n+3, 0, 0) ⊢* (2*n+4, 0, 2*n+3, 0, 0)
  apply stepStar_trans (b_to_a (a := 0) (c := 2 * n + 3))
  ring_nf; finish

-- Main cycle: (n+2, 0, n+1, 0, 0) ⊢⁺ (2*n+4, 0, 2*n+3, 0, 0)
theorem cycle : ⟨n + 2, 0, n + 1, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 4, 0, 2 * n + 3, 0, 0⟩ := by
  -- Phase 1: drain c to e
  rw [show (n + 1 : ℕ) = 0 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_e (a := n + 2) (c := 0) (e := 0))
  simp only [Nat.zero_add]
  -- Phase 2: rule 5: (n+2, 0, 0, 0, n+1) -> (n+1, 1, 1, 0, n+1)
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  simp only [Nat.succ_eq_add_one, Nat.zero_add]
  -- Phase 3: zigzag
  rw [show n + 1 = 1 + n from by ring]
  apply stepStar_trans (zigzag n 1)
  -- Phase 4: tail
  exact stepPlus_stepStar tail

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (C := fun n ↦ ⟨n + 2, 0, n + 1, 0, 0⟩) (i₀ := 0)
  intro n
  exact ⟨2 * n + 2, cycle⟩

end Sz22_2003_unofficial_403
