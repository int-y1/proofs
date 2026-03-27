import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #411: [25/63, 1/55, 36/5, 11/3, 35/2]

Vector representation:
```
 0 -2  2 -1  0
 0  0 -1  0 -1
 2  2 -1  0  0
 0 -1  0  0  1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_411

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R1 + R3 pair: (a, 2, c, d+1, 0) → (a+2, 2, c+1, d, 0)
theorem r1r3_pair : ∀ a c d,
    ⟨a, 2, c, d+1, 0⟩ [fm]⊢* ⟨a+2, 2, c+1, d, 0⟩ := by
  intro a c d
  step fm; step fm; finish

-- Iterate R1/R3 pairs j times
theorem r1r3_iter : ∀ j, ∀ a c d,
    ⟨a, 2, c, d+j, 0⟩ [fm]⊢* ⟨a+2*j, 2, c+j, d, 0⟩ := by
  intro j; induction j with
  | zero => intro a c d; exists 0
  | succ j ih =>
    intro a c d
    rw [show d + (j + 1) = (d + j) + 1 from by ring]
    apply stepStar_trans (r1r3_pair _ _ _)
    apply stepStar_trans (ih (a + 2) (c + 1) d)
    rw [show a + 2 + 2 * j = a + 2 * (j + 1) from by ring,
        show c + 1 + j = c + (j + 1) from by ring]
    exists 0

-- R3 chain: consume c, grow a and b
theorem r3_chain : ∀ j, ∀ a b,
    ⟨a, b, j, 0, 0⟩ [fm]⊢* ⟨a+2*j, b+2*j, 0, 0, 0⟩ := by
  intro j; induction j with
  | zero => intro a b; exists 0
  | succ j ih =>
    intro a b
    step fm
    apply stepStar_trans (ih (a + 2) (b + 2))
    rw [show a + 2 + 2 * j = a + 2 * (j + 1) from by ring,
        show b + 2 + 2 * j = b + 2 * (j + 1) from by ring]
    exists 0

-- R4 chain: consume b, grow e
theorem r4_chain : ∀ j, ∀ a e,
    ⟨a, j, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+j⟩ := by
  intro j; induction j with
  | zero => intro a e; exists 0
  | succ j ih =>
    intro a e
    step fm
    apply stepStar_trans (ih a (e + 1))
    rw [show e + 1 + j = e + (j + 1) from by ring]
    exists 0

-- R5/R2 pair: (a+1, 0, 0, d, e+1) → (a, 0, 0, d+1, e)
theorem r5r2_pair : ∀ a d e,
    ⟨a+1, 0, 0, d, e+1⟩ [fm]⊢* ⟨a, 0, 0, d+1, e⟩ := by
  intro a d e
  step fm; step fm; finish

-- Iterate R5/R2 pairs j times
theorem r5r2_iter : ∀ j, ∀ a d e,
    ⟨a+j, 0, 0, d, e+j⟩ [fm]⊢* ⟨a, 0, 0, d+j, e⟩ := by
  intro j; induction j with
  | zero => intro a d e; exists 0
  | succ j ih =>
    intro a d e
    rw [show a + (j + 1) = (a + j) + 1 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    apply stepStar_trans (r5r2_pair _ _ _)
    apply stepStar_trans (ih a (d + 1) e)
    rw [show d + 1 + j = d + (j + 1) from by ring]
    exists 0

-- Main transition: (A+1, 0, 0, d, 0) ⊢⁺ (A+2*d+2, 0, 0, 2*d+4, 0)
theorem main_trans (A d : ℕ) :
    ⟨A+1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨A+2*d+2, 0, 0, 2*d+4, 0⟩ := by
  -- R5: (A+1, 0, 0, d, 0) -> (A, 0, 1, d+1, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨A + 1, 0, 0, d, 0⟩ = some ⟨A, 0, 1, d + 1, 0⟩; rfl
  -- R3: (A, 0, 1, d+1, 0) -> (A+2, 2, 0, d+1, 0)
  apply stepStar_trans
  · show ⟨A, 0, 1, d + 1, 0⟩ [fm]⊢* ⟨A + 2, 2, 0, d + 1, 0⟩
    step fm; finish
  -- R1/R3 loop d+1 times: (A+2, 2, 0, d+1, 0) ->* (A+2*d+4, 2, d+1, 0, 0)
  apply stepStar_trans
  · have h := r1r3_iter (d+1) (A+2) 0 0
    simp only [(by ring : 0 + (d + 1) = d + 1),
               (by ring : A + 2 + 2 * (d + 1) = A + 2 * d + 4)] at h
    exact h
  -- R3 chain d+1 times: (A+2*d+4, 2, d+1, 0, 0) ->* (A+4*d+6, 2*d+4, 0, 0, 0)
  apply stepStar_trans
  · have h := r3_chain (d+1) (A+2*d+4) 2
    rw [show A + 2 * d + 4 + 2 * (d + 1) = A + 4 * d + 6 from by ring,
        show 2 + 2 * (d + 1) = 2 * d + 4 from by ring] at h
    exact h
  -- R4 chain 2*d+4 times: (A+4*d+6, 2*d+4, 0, 0, 0) ->* (A+4*d+6, 0, 0, 0, 2*d+4)
  apply stepStar_trans
  · have h := r4_chain (2*d+4) (A+4*d+6) 0
    simp only [(by ring : 0 + (2 * d + 4) = 2 * d + 4)] at h
    exact h
  -- R5/R2 chain 2*d+4 times: (A+4*d+6, 0, 0, 0, 2*d+4) ->* (A+2*d+2, 0, 0, 2*d+4, 0)
  have h := r5r2_iter (2*d+4) (A+2*d+2) 0 0
  simp only [(by ring : A + 2 * d + 2 + (2 * d + 4) = A + 4 * d + 6),
             (by ring : 0 + (2 * d + 4) = 2 * d + 4)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0+1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, d⟩ ↦ ⟨A+1, 0, 0, d, 0⟩) ⟨0, 0⟩
  intro ⟨A, d⟩
  exact ⟨⟨A+2*d+1, 2*d+4⟩, main_trans A d⟩

end Sz22_2003_unofficial_411
