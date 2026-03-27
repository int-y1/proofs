import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #349: [2/15, 1/3, 11319/2, 25/539, 3/7]

Vector representation:
```
 1 -1 -1  0  0
 0 -1  0  0  0
-1  1  0  3  1
 0  0  2 -2 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_349

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+3, e+1⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- One iteration of the consume loop: rule 1 then rule 3
theorem consume_one : ∀ c d e,
    ⟨0, 1, c+1, d, e⟩ [fm]⊢* ⟨0, 1, c, d+3, e+1⟩ := by
  intro c d e
  step fm; step fm; finish

-- Iterate consume loop j times
theorem consume_iter : ∀ j, ∀ c d e,
    ⟨0, 1, c+j, d, e⟩ [fm]⊢* ⟨0, 1, c, d+3*j, e+j⟩ := by
  intro j; induction j with
  | zero => intro c d e; exists 0
  | succ j ih =>
    intro c d e
    rw [show c + (j + 1) = (c + j) + 1 from by ring]
    apply stepStar_trans (consume_one _ _ _)
    apply stepStar_trans (ih _ _ _)
    rw [show d + 3 + 3 * j = d + 3 * (j + 1) from by ring,
        show e + 1 + j = e + (j + 1) from by ring]
    finish

-- Rule 4 iteration
theorem rule4_iter : ∀ j, ∀ c d,
    ⟨0, 0, c, d+2*j, j⟩ [fm]⊢* ⟨0, 0, c+2*j, d, 0⟩ := by
  intro j; induction j with
  | zero => intro c d; simp; exists 0
  | succ j ih =>
    intro c d
    rw [show d + 2 * (j + 1) = (d + 2 * j) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) d)
    rw [show c + 2 + 2 * j = c + 2 * (j + 1) from by ring]
    finish

-- Rule 5 step: need to case split on c and d for definitional reduction
theorem rule5_step (c d : ℕ) : fm ⟨0, 0, c, d+1, 0⟩ = some ⟨0, 1, c, d, 0⟩ := by
  cases c with
  | zero => cases d with
    | zero => rfl
    | succ d => rfl
  | succ c => cases d with
    | zero => rfl
    | succ d => rfl

-- Rule 2 step on zero c
theorem rule2_step (d e : ℕ) : fm ⟨0, 1, 0, d, e⟩ = some ⟨0, 0, 0, d, e⟩ := by
  cases d with
  | zero => cases e with
    | zero => rfl
    | succ e => rfl
  | succ d => cases e with
    | zero => rfl
    | succ e => rfl

-- Main transition: (0, 0, C+1, D+1, 0) ⊢+ (0, 0, 2*C+2, D+C+1, 0)
theorem main_trans (C D : ℕ) :
    ⟨0, 0, C+1, D+1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*C+2, D+C+1, 0⟩ := by
  -- Phase 1: Rule 5
  apply step_stepStar_stepPlus (rule5_step (C+1) D)
  -- Phase 2: Consume loop (C+1 iterations)
  apply stepStar_trans
  · have h := consume_iter (C+1) 0 D 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 2b: Rule 2
  apply stepStar_trans
  · exact step_stepStar (rule2_step (D + 3 * (C + 1)) (C + 1))
  -- Phase 3: Rule 4 loop (C+1 iterations)
  have h := rule4_iter (C+1) 0 (D+C+1)
  simp only [Nat.zero_add] at h
  rw [show D + C + 1 + 2 * (C + 1) = D + 3 * (C + 1) from by ring,
      show 2 * (C + 1) = 2 * C + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨C, D⟩ ↦ ⟨0, 0, C+1, D+1, 0⟩) ⟨1, 0⟩
  intro ⟨C, D⟩
  exact ⟨⟨2*C+1, D+C⟩, main_trans C D⟩

end Sz22_2003_unofficial_349
