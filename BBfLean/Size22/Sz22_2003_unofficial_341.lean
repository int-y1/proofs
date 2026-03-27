import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #341: [2/105, 3/22, 25/2, 77/5, 12/11]

Vector representation:
```
 1 -1 -1 -1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0 -1  1  1
 2  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_341

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

-- Phase 1: Transfer a to c (rule 3), each step doubles
-- (a+j, 0, c, 0, 0) ->* (a, 0, c+2*j, 0, 0)
theorem a_to_c : ∀ j a c,
    ⟨a+j, 0, c, 0, 0⟩ [fm]⊢* ⟨a, 0, c+2*j, 0, 0⟩ := by
  intro j; induction' j with j ih <;> intro a c
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 2: Transfer c to d and e (rule 4)
-- (0, 0, c+j, d, e) ->* (0, 0, c, d+j, e+j)
theorem c_to_de : ∀ j c d e,
    ⟨0, 0, c+j, d, e⟩ [fm]⊢* ⟨0, 0, c, d+j, e+j⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show c + (j + 1) = (c + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 3: Consume e in triplets (rules 5, 2, 2)
-- (0, b, 0, d, e+3) -> (2, b+1, 0, d, e+2) -> (1, b+2, 0, d, e+1) -> (0, b+3, 0, d, e)
theorem e_consume_one : ∀ b d e,
    ⟨0, b, 0, d, e+3⟩ [fm]⊢* ⟨0, b+3, 0, d, e⟩ := by
  intro b d e
  step fm; step fm; step fm
  ring_nf; finish

theorem e_consume_iter : ∀ j b d e,
    ⟨0, b, 0, d, e+3*j⟩ [fm]⊢* ⟨0, b+3*j, 0, d, e⟩ := by
  intro j; induction' j with j ih <;> intro b d e
  · exists 0
  rw [show e + 3 * (j + 1) = (e + 3 * j) + 3 from by ring]
  apply stepStar_trans (e_consume_one _ _ _)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Tail: consume leftover e=2 (rules 5, 2)
-- (0, b, 0, d, 2) -> (2, b+1, 0, d, 1) -> (1, b+2, 0, d, 0)
theorem e_tail2 : ∀ b d,
    ⟨0, b, 0, d, 2⟩ [fm]⊢* ⟨1, b+2, 0, d, 0⟩ := by
  intro b d; step fm; step fm; finish

-- Tail: consume leftover e=1 (rule 5)
-- (0, b, 0, d, 1) -> (2, b+1, 0, d, 0)
theorem e_tail1 : ∀ b d,
    ⟨0, b, 0, d, 1⟩ [fm]⊢* ⟨2, b+1, 0, d, 0⟩ := by
  intro b d; step fm; finish

-- Phase 4: Reduce (a, 2m+2, 0, 2m+2, 0) with a>=1 (rules 3, 1, 1)
-- (a+1, b+2, 0, d+2, 0) -> (a, b+2, 2, d+2, 0) -> (a+1, b+1, 1, d+1, 0) -> (a+2, b, 0, d, 0)
theorem reduce_one : ∀ a b d,
    ⟨a+1, b+2, 0, d+2, 0⟩ [fm]⊢* ⟨a+2, b, 0, d, 0⟩ := by
  intro a b d; step fm; step fm; step fm; finish

theorem reduce_iter : ∀ j a b d,
    ⟨a+1, b+2*j, 0, d+2*j, 0⟩ [fm]⊢* ⟨a+1+j, b, 0, d, 0⟩ := by
  intro j; induction' j with j ih <;> intro a b d
  · exists 0
  rw [show b + 2 * (j + 1) = (b + 2 * j) + 2 from by ring,
      show d + 2 * (j + 1) = (d + 2 * j) + 2 from by ring]
  apply stepStar_trans (reduce_one _ _ _)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: (3k+1, 0, 0, 0, 0) ⊢⁺ (3(k+1)+1, 0, 0, 0, 0)
theorem main_trans (k : ℕ) :
    ⟨3*k+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨3*(k+1)+1, 0, 0, 0, 0⟩ := by
  -- First half: (3k+1, 0,0,0,0) ⊢⁺ (3k+2, 0,0,0,0)
  apply stepStar_stepPlus_stepPlus
  -- Phase 1: (3k+1, 0, 0, 0, 0) ->* (0, 0, 6k+2, 0, 0)
  · apply stepStar_trans
    · have h := a_to_c (3*k+1) 0 0
      simp only [(by ring : 0 + (3*k+1) = 3*k+1), (by ring : 0 + 2*(3*k+1) = 6*k+2)] at h
      exact h
    -- Phase 2: (0, 0, 6k+2, 0, 0) ->* (0, 0, 0, 6k+2, 6k+2)
    apply stepStar_trans
    · have h := c_to_de (6*k+2) 0 0 0
      simp only [(by ring : 0 + (6*k+2) = 6*k+2)] at h
      exact h
    -- Phase 3: consume e = 6k+2 = 3*(2k) + 2
    apply stepStar_trans
    · have h := e_consume_iter (2*k) 0 (6*k+2) 2
      simp only [(by ring : 2 + 3*(2*k) = 6*k+2), (by ring : 0 + 3*(2*k) = 6*k)] at h
      exact h
    -- Tail: (0, 6k, 0, 6k+2, 2) ->* (1, 6k+2, 0, 6k+2, 0)
    apply stepStar_trans
    · exact e_tail2 (6*k) (6*k+2)
    -- Phase 4: (1, 6k+2, 0, 6k+2, 0) ->* (3k+2, 0, 0, 0, 0)
    have h := reduce_iter (3*k+1) 0 0 0
    simp only [(by ring : 0 + 2*(3*k+1) = 6*k+2), (by ring : 0 + 1 + (3*k+1) = 3*k+2)] at h
    exact h
  -- Second half: (3k+2, 0,0,0,0) ⊢⁺ (3k+4, 0,0,0,0)
  -- Phase 5: (3k+2, 0, 0, 0, 0) ->* (0, 0, 6k+4, 0, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨3*k+2, 0, 0, 0, 0⟩ = some ⟨3*k+1, 0, 2, 0, 0⟩; rfl
  apply stepStar_trans
  · have h := a_to_c (3*k+1) 0 2
    simp only [(by ring : 0 + (3*k+1) = 3*k+1), (by ring : 2 + 2*(3*k+1) = 6*k+4)] at h
    exact h
  -- Phase 6: (0, 0, 6k+4, 0, 0) ->* (0, 0, 0, 6k+4, 6k+4)
  apply stepStar_trans
  · have h := c_to_de (6*k+4) 0 0 0
    simp only [(by ring : 0 + (6*k+4) = 6*k+4)] at h
    exact h
  -- Phase 7: consume e = 6k+4 = 3*(2k+1) + 1
  apply stepStar_trans
  · have h := e_consume_iter (2*k+1) 0 (6*k+4) 1
    simp only [(by ring : 1 + 3*(2*k+1) = 6*k+4), (by ring : 0 + 3*(2*k+1) = 6*k+3)] at h
    exact h
  -- Tail: (0, 6k+3, 0, 6k+4, 1) ->* (2, 6k+4, 0, 6k+4, 0)
  apply stepStar_trans
  · exact e_tail1 (6*k+3) (6*k+4)
  -- Phase 8: (2, 6k+4, 0, 6k+4, 0) ->* (3k+4, 0, 0, 0, 0)
  have h := reduce_iter (3*k+2) 1 0 0
  simp only [(by ring : 0 + 2*(3*k+2) = 6*k+4), (by ring : 1 + 1 + (3*k+2) = 3*k+4),
             (by ring : 3*k+4 = 3*(k+1)+1)] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  exact progress_nonhalt_simple (fm := fm) (fun k ↦ ⟨3*k+1, 0, 0, 0, 0⟩) 0 (fun k ↦ ⟨k+1, main_trans k⟩)

end Sz22_2003_unofficial_341
