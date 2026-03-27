import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #429: [27/175, 20/3, 1/40, 147/2]

Vector representation:
```
 0  3 -2 -1
 2 -1  1  0
-3  0 -1  0
-1  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_429

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+2, d+1⟩ => some ⟨a, b+3, c, d⟩
  | ⟨a, b+1, c, d⟩ => some ⟨a+2, b, c+1, d⟩
  | ⟨a+3, b, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+1, c, d+2⟩
  | _ => none

-- R3 single step: (a+3, 0, c+1, 0) -> (a, 0, c, 0)
theorem r3_step (a c : ℕ) :
    ⟨a + 3, 0, c + 1, 0⟩ [fm]⊢ (⟨a, 0, c, 0⟩ : Q) := by
  show fm ⟨a + 3, 0, c + 1, 0⟩ = some ⟨a, 0, c, 0⟩
  cases c with
  | zero => rfl
  | succ c => rfl

-- Phase 2 inner step: (a, b+2, 0, d+1) -> 3 steps -> (a+4, b+3, 0, d)
theorem phase2_step (a b d : ℕ) :
    ⟨a, b + 2, 0, d + 1⟩ [fm]⊢* (⟨a + 4, b + 3, 0, d⟩ : Q) := by
  step fm; step fm; step fm; finish

-- Phase 2 loop: (a, b+2, 0, d+k) ->* (a+4*k, b+2+k, 0, d)
theorem phase2_loop : ∀ k a b d,
    ⟨a, b + 2, 0, d + k⟩ [fm]⊢* (⟨a + 4 * k, b + 2 + k, 0, d⟩ : Q) := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih a b (d + 1))
    rw [show b + 2 + k = (b + k) + 2 from by ring]
    apply stepStar_trans (phase2_step (a + 4 * k) (b + k) d)
    rw [show a + 4 * k + 4 = a + 4 * (k + 1) from by ring,
        show b + k + 3 = b + 2 + (k + 1) from by ring]
    finish

-- R2 chain with d=0: (a, k, c, 0) ->* (a+2*k, 0, c+k, 0)
theorem r2_chain : ∀ k a c,
    ⟨a, k, c, 0⟩ [fm]⊢* (⟨a + 2 * k, 0, c + k, 0⟩ : Q) := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    step fm
    apply stepStar_trans (ih (a + 2) (c + 1))
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring,
        show c + 1 + k = c + (k + 1) from by ring]
    finish

-- R3 chain with d=0, b=0: (a+3*k, 0, k, 0) ->* (a, 0, 0, 0)
theorem r3_chain : ∀ k a,
    ⟨a + 3 * k, 0, k, 0⟩ [fm]⊢* (⟨a, 0, 0, 0⟩ : Q) := by
  intro k; induction k with
  | zero => intro a; exists 0
  | succ k ih =>
    intro a
    rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring]
    apply stepStar_trans (c₂ := ⟨a + 3 * k, 0, k, 0⟩)
    · exact step_stepStar (r3_step (a + 3 * k) k)
    exact ih a

-- Drain step: (2k+3, 0, 0, d) -> 3 steps -> (2k+1, 0, 0, d+2)
theorem drain_step (k d : ℕ) :
    ⟨2 * k + 3, 0, 0, d⟩ [fm]⊢* (⟨2 * k + 1, 0, 0, d + 2⟩ : Q) := by
  apply stepStar_trans (c₂ := ⟨2 * k + 2, 1, 0, d + 2⟩)
  · apply step_stepStar
    show fm ⟨2 * k + 3, 0, 0, d⟩ = some ⟨2 * k + 2, 1, 0, d + 2⟩
    cases d <;> rfl
  apply stepStar_trans (c₂ := ⟨2 * k + 4, 0, 1, d + 2⟩)
  · apply step_stepStar
    show fm ⟨2 * k + 2, 1, 0, d + 2⟩ = some ⟨2 * k + 4, 0, 1, d + 2⟩
    rfl
  apply step_stepStar
  show fm ⟨2 * k + 4, 0, 1, d + 2⟩ = some ⟨2 * k + 1, 0, 0, d + 2⟩
  rfl

-- Drain loop: (2*k+1, 0, 0, d) ->* (1, 0, 0, d+2*k)
theorem drain_loop : ∀ k d,
    ⟨2 * k + 1, 0, 0, d⟩ [fm]⊢* (⟨1, 0, 0, d + 2 * k⟩ : Q) := by
  intro k; induction k with
  | zero => intro d; exists 0
  | succ k ih =>
    intro d
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by ring]
    apply stepStar_trans (drain_step k d)
    apply stepStar_trans (ih (d + 2))
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]
    finish

-- Main transition: (1, 0, 0, 2*n) ⊢⁺ (1, 0, 0, 6*n+8)
theorem main_trans (n : ℕ) :
    ⟨1, 0, 0, 2 * n⟩ [fm]⊢⁺ (⟨1, 0, 0, 6 * n + 8⟩ : Q) := by
  -- Phase 1: (1,0,0,2n) -> 5 steps -> (3, 3, 0, 2n+3)
  apply step_stepStar_stepPlus
  · show fm ⟨1, 0, 0, 2 * n⟩ = some ⟨0, 1, 0, 2 * n + 2⟩
    cases n <;> rfl
  step fm
  apply stepStar_trans (c₂ := ⟨1, 1, 1, 2 * n + 4⟩)
  · apply step_stepStar
    show fm ⟨2, 0, 1, 2 * n + 2⟩ = some ⟨1, 1, 1, 2 * n + 4⟩
    cases n <;> rfl
  step fm
  apply stepStar_trans (c₂ := ⟨3, 3, 0, 2 * n + 3⟩)
  · apply step_stepStar
    show fm ⟨3, 0, 2, 2 * n + 4⟩ = some ⟨3, 3, 0, 2 * n + 3⟩
    rfl
  -- Phase 2: (3, 3, 0, 2n+3) -> loop 2n+3 times -> (8n+15, 2n+6, 0, 0)
  apply stepStar_trans
  · show ⟨3, 3, 0, 2 * n + 3⟩ [fm]⊢* ⟨8 * n + 15, 2 * n + 6, 0, 0⟩
    have h := phase2_loop (2 * n + 3) 3 1 0
    rw [show 1 + 2 = 3 from rfl,
        show 0 + (2 * n + 3) = 2 * n + 3 from by ring,
        show 3 + 4 * (2 * n + 3) = 8 * n + 15 from by ring,
        show 1 + 2 + (2 * n + 3) = 2 * n + 6 from by ring] at h
    exact h
  -- Phase 3: R2 chain (2n+6 times) -> (12n+27, 0, 2n+6, 0)
  apply stepStar_trans
  · show ⟨8 * n + 15, 2 * n + 6, 0, 0⟩ [fm]⊢* ⟨12 * n + 27, 0, 2 * n + 6, 0⟩
    have h := r2_chain (2 * n + 6) (8 * n + 15) 0
    rw [show 8 * n + 15 + 2 * (2 * n + 6) = 12 * n + 27 from by ring,
        show 0 + (2 * n + 6) = 2 * n + 6 from by ring] at h
    exact h
  -- Phase 4: R3 chain (2n+6 times) -> (6n+9, 0, 0, 0)
  apply stepStar_trans
  · show ⟨12 * n + 27, 0, 2 * n + 6, 0⟩ [fm]⊢* ⟨6 * n + 9, 0, 0, 0⟩
    have h := r3_chain (2 * n + 6) (6 * n + 9)
    rw [show 6 * n + 9 + 3 * (2 * n + 6) = 12 * n + 27 from by ring] at h
    exact h
  -- Phase 5: drain (6n+9, 0, 0, 0) -> (1, 0, 0, 6n+8)
  show ⟨6 * n + 9, 0, 0, 0⟩ [fm]⊢* ⟨1, 0, 0, 6 * n + 8⟩
  have h := drain_loop (3 * n + 4) 0
  rw [show 2 * (3 * n + 4) + 1 = 6 * n + 9 from by ring,
      show 0 + 2 * (3 * n + 4) = 6 * n + 8 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨1, 0, 0, 2 * n⟩) 0
  intro n
  exact ⟨3 * n + 4, by
    rw [show 2 * (3 * n + 4) = 6 * n + 8 from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_429
