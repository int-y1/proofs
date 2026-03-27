import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #354: [2/15, 1/98, 4719/2, 35/11, 2/91]

Vector representation:
```
 1 -1 -1  0  0  0
-1  0  0 -2  0  0
-1  1  0  0  2  1
 0  0  1  1 -1  0
 1  0  0 -1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_354

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+2, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+2, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- Rule 4 loop: apply rule 4 k times
theorem rule4_loop : ∀ k c d f, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c + k, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) (d + 1) f)
    ring_nf; finish

-- Drain pairs: k pairs of rule5 + rule2
theorem drain_pairs : ∀ k c f, ⟨0, 0, c, 3 * k + 2, 0, f + k + 1⟩ [fm]⊢* ⟨0, 0, c, 2, 0, f + 1⟩ := by
  intro k; induction' k with k ih <;> intro c f
  · simp; exists 0
  · step fm; step fm
    exact ih c f

-- Drain finish: rule5 then rule3
theorem drain_finish : ∀ c f, ⟨0, 0, c, 2, 0, f + 1⟩ [fm]⊢* ⟨0, 1, c, 1, 2, f + 1⟩ := by
  intro c f
  step fm; step fm; finish

-- Inner loop: k iterations of rule1 + rule3
theorem inner_loop : ∀ k c e f, ⟨0, 1, c + k, 1, e, f⟩ [fm]⊢* ⟨0, 1, c, 1, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih c (e + 2) (f + 1))
    rw [show e + 2 + 2 * k = e + 2 * (k + 1) from by ring,
        show f + 1 + k = f + (k + 1) from by ring]
    finish

-- Final 3 steps: rule4 + rule1 + rule2
theorem final_steps : ∀ e f, ⟨0, 1, 0, 1, e + 1, f⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, e, f⟩ := by
  intro e f
  step fm; step fm; step fm; finish

-- Main cycle
theorem main_cycle (m : ℕ) :
    ⟨0, 0, 0, 0, 3 * m + 2, 2 * m + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 6 * m + 5, 4 * m + 4⟩ := by
  -- Phase A: rule4 loop (3m+2 steps)
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 0, 0, 3 * m + 2, 2 * m + 2⟩ [fm]⊢* ⟨0, 0, 3 * m + 2, 3 * m + 2, 0, 2 * m + 2⟩
    have h := rule4_loop (3 * m + 2) 0 0 (2 * m + 2)
    simp only [Nat.zero_add] at h; exact h
  -- Phase B: drain pairs + finish
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 3 * m + 2, 3 * m + 2, 0, 2 * m + 2⟩ [fm]⊢* ⟨0, 1, 3 * m + 2, 1, 2, m + 2⟩
    apply stepStar_trans (c₂ := ⟨0, 0, 3 * m + 2, 2, 0, m + 2⟩)
    · have h := drain_pairs m (3 * m + 2) (m + 1)
      rw [show m + 1 + m + 1 = 2 * m + 2 from by ring] at h; exact h
    · have h := drain_finish (3 * m + 2) (m + 1)
      rw [show m + 1 + 1 = m + 2 from by ring] at h; exact h
  -- Phase C: inner loop
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 1, 3 * m + 2, 1, 2, m + 2⟩ [fm]⊢* ⟨0, 1, 0, 1, 6 * m + 6, 4 * m + 4⟩
    have h := inner_loop (3 * m + 2) 0 2 (m + 2)
    rw [show 0 + (3 * m + 2) = 3 * m + 2 from by ring,
        show 2 + 2 * (3 * m + 2) = 6 * m + 6 from by ring,
        show m + 2 + (3 * m + 2) = 4 * m + 4 from by ring] at h; exact h
  -- Phase D: final steps
  show ⟨0, 1, 0, 1, 6 * m + 6, 4 * m + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 6 * m + 5, 4 * m + 4⟩
  have h := final_steps (6 * m + 5) (4 * m + 4)
  rw [show 6 * m + 5 + 1 = 6 * m + 6 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 0, 3 * n + 2, 2 * n + 2⟩) 0
  intro n
  exact ⟨2 * n + 1, by
    rw [show 3 * (2 * n + 1) + 2 = 6 * n + 5 from by ring,
        show 2 * (2 * n + 1) + 2 = 4 * n + 4 from by ring]
    exact main_cycle n⟩

end Sz22_2003_unofficial_354
