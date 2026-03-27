import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #379: [2/15, 99/14, 125/2, 7/11, 22/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  3  0  0
 0  0  0  1 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_379

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- Rule 4 repeated: transfer e to d (with a=0 so R1-R3 don't match)
theorem e_to_d (k : ℕ) : ∀ d, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- Rule 3 repeated: convert a to c (with b=0, d=0, so R3 matches before R4)
theorem a_to_c (k : ℕ) : ∀ c, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e⟩ := by
  induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 3))
    ring_nf; finish

-- One round of R2 + R1 + R1:
-- (j+1, 0, c+2, d+1, j+1) ⊢* (j+2, 0, c, d, j+2)
theorem r2r1r1 : ⟨j+1, 0, c + 2, d + 1, j + 1⟩ [fm]⊢* ⟨j + 2, 0, c, d, j + 2⟩ := by
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm
  step fm
  ring_nf; finish

-- Inner loop: k rounds of R2+R1+R1
theorem inner_loop (k : ℕ) : ∀ c d j,
    ⟨j + 1, 0, c + 2 * k, d + k, j + 1⟩ [fm]⊢* ⟨j + 1 + k, 0, c, d, j + 1 + k⟩ := by
  induction k with
  | zero => intro c d j; exists 0
  | succ k ih =>
    intro c d j
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans r2r1r1
    rw [show j + 1 + (k + 1) = (j + 2) + k from by ring]
    exact ih c d (j + 1)

-- Case e = 0: (0, 0, c+3, 0, 0) ⊢⁺ (0, 0, c+5, 0, 1)
theorem case_zero : ⟨0, 0, c + 3, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, c + 5, 0, 1⟩ := by
  rw [show c + 3 = (c + 2) + 1 from by ring]
  step fm
  step fm
  ring_nf; finish

-- Case e = n+1: (0, 0, c + 2*n + 5, 0, n+1) ⊢⁺ (0, 0, c + 3*n + 8, 0, n+2)
theorem case_succ (n : ℕ) :
    ⟨0, 0, c + 2 * n + 5, 0, n + 1⟩ [fm]⊢⁺ ⟨0, 0, c + 3 * n + 8, 0, n + 2⟩ := by
  -- Phase 1: e_to_d
  have h1 : ⟨0, 0, c + 2 * n + 5, 0, 0 + (n + 1)⟩ [fm]⊢*
      ⟨0, 0, c + 2 * n + 5, 0 + (n + 1), 0⟩ := e_to_d (n + 1) 0
  simp only [Nat.zero_add] at h1
  -- Phase 2: R5
  have h2 : ⟨0, 0, (c + 2 * n + 4) + 1, n + 1, 0⟩ [fm]⊢ ⟨1, 0, c + 2 * n + 4, n + 1, 1⟩ := by
    unfold fm; rfl
  rw [show (c + 2 * n + 4) + 1 = c + 2 * n + 5 from by ring] at h2
  -- Phase 3: inner_loop
  have h3 : ⟨0 + 1, 0, (c + 2) + 2 * (n + 1), 0 + (n + 1), 0 + 1⟩ [fm]⊢*
      ⟨0 + 1 + (n + 1), 0, c + 2, 0, 0 + 1 + (n + 1)⟩ := inner_loop (n + 1) (c + 2) 0 0
  simp only [Nat.zero_add] at h3
  rw [show (c + 2) + 2 * (n + 1) = c + 2 * n + 4 from by ring,
      show 1 + (n + 1) = n + 2 from by ring] at h3
  -- Phase 4: a_to_c
  have h4 : ⟨0 + (n + 2), 0, c + 2, 0, n + 2⟩ [fm]⊢*
      ⟨0, 0, (c + 2) + 3 * (n + 2), 0, n + 2⟩ := a_to_c (n + 2) (c + 2) (a := 0) (e := n + 2)
  simp only [Nat.zero_add] at h4
  rw [show (c + 2) + 3 * (n + 2) = c + 3 * n + 8 from by ring] at h4
  -- Combine: h1 : ⊢*, h2 : step, h3 : ⊢*, h4 : ⊢*
  -- stepStar (h1) then step (h2) gives stepPlus
  -- then stepStar (h3) then stepStar (h4)
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2 (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ c ≥ 2 * e + 3)
  · intro q ⟨c, e, hq, hc⟩; subst hq
    rcases e with _ | n
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 3 := ⟨c - 3, by omega⟩
      exact ⟨⟨0, 0, c' + 5, 0, 1⟩, ⟨c' + 5, 1, rfl, by omega⟩, case_zero⟩
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 * n + 5 := ⟨c - 2 * n - 5, by omega⟩
      exact ⟨⟨0, 0, c' + 3 * n + 8, 0, n + 2⟩,
             ⟨c' + 3 * n + 8, n + 2, rfl, by omega⟩,
             case_succ n⟩
  · exact ⟨3, 0, rfl, by omega⟩

end Sz22_2003_unofficial_379
