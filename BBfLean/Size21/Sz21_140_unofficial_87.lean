import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #87: [5/6, 539/2, 4/35, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  0
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_87

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase 1: R4 repeated: transfer d to b (when a=0, c=0)
-- (0, b, 0, d+k, e) ->* (0, b+k, 0, d, e)
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b d, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b d
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k b d

-- Phase 2: One interleaved round (5 steps): R5, R1, R3, R1, R1
-- (0, b+3, c, 0, e+1) -> (0, b, c+2, 0, e)
theorem one_round : ∀ b c e, ⟨0, b+3, c, 0, e+1⟩ [fm]⊢* ⟨0, b, c+2, 0, e⟩ := by
  intro b c e
  -- R5: (0, b+3, c, 0, e+1) -> (1, b+3, c, 1, e)
  step fm
  -- R1: (1, b+3, c, 1, e) -> (0, b+2, c+1, 1, e)
  rw [show (1 : ℕ) = 0 + 1 from rfl, show b + 3 = (b + 2) + 1 from by ring]
  step fm
  -- R3: (0, b+2, c+1, 1, e) -> (2, b+2, c, 0, e)
  step fm
  -- R1: (2, b+2, c, 0, e) -> (1, b+1, c+1, 0, e)
  rw [show (2 : ℕ) = 1 + 1 from rfl, show b + 2 = (b + 1) + 1 from by ring]
  step fm
  -- R1: (1, b+1, c+1, 0, e) -> (0, b, c+2, 0, e)
  rw [show (1 : ℕ) = 0 + 1 from rfl, show b + 1 = b + 1 from rfl]
  step fm
  ring_nf; finish

-- Phase 2: j interleaved rounds
-- (0, b+3*j, c, 0, e+j) ->* (0, b, c+2*j, 0, e)
theorem interleaved_rounds : ∀ j, ∀ b c e, ⟨0, b+3*j, c, 0, e+j⟩ [fm]⊢* ⟨0, b, c+2*j, 0, e⟩ := by
  intro j; induction' j with j ih <;> intro b c e
  · simp; exists 0
  rw [show b + 3 * (j + 1) = (b + 3) + 3 * j from by ring,
      show e + (j + 1) = (e + 1) + j from by ring]
  apply stepStar_trans (ih (b + 3) c (e + 1))
  rw [show c + 2 * j = c + 2 * j from rfl]
  apply stepStar_trans (one_round b (c + 2 * j) e)
  ring_nf; finish

-- Phase 3: Endgame with b=2 (5 steps)
-- (0, 2, c, 0, e+1) -> (0, 0, c+1, 2, e+1)
theorem endgame : ∀ c e, ⟨0, 2, c, 0, e+1⟩ [fm]⊢* ⟨0, 0, c+1, 2, e+1⟩ := by
  intro c e
  -- R5: (0, 2, c, 0, e+1) -> (1, 2, c, 1, e)
  step fm
  -- R1: (1, 2, c, 1, e) -> (0, 1, c+1, 1, e)
  rw [show (1 : ℕ) = 0 + 1 from rfl, show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  -- R3: (0, 1, c+1, 1, e) -> (2, 1, c, 0, e)
  step fm
  -- R1: (2, 1, c, 0, e) -> (1, 0, c+1, 0, e)
  rw [show (2 : ℕ) = 1 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  -- R2: (1, 0, c+1, 0, e) -> (0, 0, c+1, 2, e+1)
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  ring_nf; finish

-- Phase 4: Drain c via R3, R2, R2 pattern
-- (0, 0, c+k, d+1, e) ->* (0, 0, c, d+1+3*k, e+2*k) when d >= 1
theorem drain_c : ∀ k, ∀ c d e, ⟨0, 0, c+k, d+1, e⟩ [fm]⊢* ⟨0, 0, c, d+1+3*k, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  -- R3: (0, 0, c+k+1, d+1, e) -> (2, 0, c+k, d, e)
  step fm
  -- R2: (2, 0, c+k, d, e) -> (1, 0, c+k, d+2, e+1)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  -- R2: (1, 0, c+k, d+2, e+1) -> (0, 0, c+k, d+4, e+2)
  rw [show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show d + 2 + 2 = (d + 3) + 1 from by ring]
  apply stepStar_trans (ih c (d + 3) (e + 2))
  ring_nf; finish

-- Main transition: (0, 0, 0, 3*j+2, e) ⊢⁺ (0, 0, 0, 6*j+5, 3*j+2+e)
-- where e >= j+1
theorem main_trans (j e : ℕ) (he : e ≥ j + 1) :
    ⟨0, 0, 0, 3*j+2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 6*j+5, 3*j+2+e⟩ := by
  -- Write e = e' + (j + 1) where e' = e - (j+1)
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + (j + 1) := ⟨e - (j + 1), by omega⟩
  -- Phase 1: R4 transfer d to b (at least 1 step since d = 3*j+2 >= 2)
  -- (0, 0, 0, 3*j+2, e'+(j+1)) -> R4 -> (0, 1, 0, 3*j+1, e'+(j+1))
  -- then ->* (0, 3*j+2, 0, 0, e'+(j+1))
  -- Phase 1: R4 transfer d to b (first step gives stepPlus)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 0, 3*j+1, e'+(j+1)⟩)
  · show fm ⟨0, 0, 0, (3*j+1)+1, e'+(j+1)⟩ = some ⟨0, 0+1, 0, 3*j+1, e'+(j+1)⟩
    simp [fm]
  -- Transfer remaining d to b: (0, 1, 0, 3j+1, e') ->* (0, 3j+2, 0, 0, e')
  have phase1_rest : ⟨0, 1, 0, 3*j+1, e'+(j+1)⟩ [fm]⊢* ⟨0, 3*j+2, 0, 0, e'+(j+1)⟩ := by
    have h := @d_to_b 1 0 (3*j+1) (e'+(j+1))
    simp only [Nat.zero_add] at h
    rw [show 1 + (3 * j + 1) = 3 * j + 2 from by ring] at h
    exact h
  apply stepStar_trans phase1_rest
  -- Phase 2: j interleaved rounds
  -- (0, 3*j+2, 0, 0, e'+(j+1)) ->* (0, 2, 2*j, 0, e'+1)
  have phase2 : ⟨0, 3*j+2, 0, 0, e'+(j+1)⟩ [fm]⊢* ⟨0, 2, 2*j, 0, e'+1⟩ := by
    rw [show 3 * j + 2 = 2 + 3 * j from by ring,
        show e' + (j + 1) = (e' + 1) + j from by ring]
    have h := interleaved_rounds j 2 0 (e' + 1)
    rw [show 0 + 2 * j = 2 * j from by ring] at h
    exact h
  apply stepStar_trans phase2
  -- Phase 3: Endgame
  -- (0, 2, 2*j, 0, e'+1) ->* (0, 0, 2*j+1, 2, e'+1)
  apply stepStar_trans (endgame (2*j) e')
  -- Phase 4: Drain c
  -- (0, 0, 2*j+1, 2, e'+1) ->* (0, 0, 0, 6j+5, 3j+2+e'+(j+1))
  have phase4 : ⟨0, 0, 2*j+1, 2, e'+1⟩ [fm]⊢* ⟨0, 0, 0, 6*j+5, 3*j+2+(e'+(j+1))⟩ := by
    have h := @drain_c (2*j+1) 0 1 (e'+1)
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  exact phase4

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) -> R2 -> (0,0,0,2,1)
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  -- (0, 0, 0, 2, 1) = C(0, 1) where C(j, e) = (0, 0, 0, 3j+2, e)
  -- Use progress_nonhalt with predicate
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ j e, q = ⟨0, 0, 0, 3*j+2, e⟩ ∧ e ≥ j + 1)
  · intro c ⟨j, e, hq, he⟩; subst hq
    exact ⟨⟨0, 0, 0, 6*j+5, 3*j+2+e⟩,
           ⟨2*j+1, 3*j+2+e, by ring_nf, by omega⟩,
           main_trans j e he⟩
  · exact ⟨0, 1, by ring_nf, by omega⟩
