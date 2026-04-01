import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1262: [5/6, 8/35, 77/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 3  0 -1 -1  0
-1  0  0  1  1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1262

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 drain: move d to b
theorem r4_drain : ∀ k b d e, ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b + 1) d e); ring_nf; finish

-- R3 drain: move a to d and e
theorem r3_drain : ∀ k D E, ⟨k, (0 : ℕ), 0, D, E⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), 0, D + k, E + k⟩ := by
  intro k; induction' k with k ih <;> intro D E
  · exists 0
  · apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨k + 1, 0, 0, D, E⟩ : Q) [fm]⊢ ⟨k, 0, 0, D + 1, E + 1⟩))
    apply stepStar_trans (ih (D + 1) (E + 1)); ring_nf; finish

-- R2-R3 chain: each round consumes one from c, adds 2 to a, adds 1 to e
theorem r2r3_chain : ∀ k A c E, ⟨A, (0 : ℕ), c + k, 1, E⟩ [fm]⊢* ⟨A + 2 * k, (0 : ℕ), c, 1, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A c E
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨A, 0, (c + k) + 1, 1, E⟩ : Q) [fm]⊢ ⟨A + 3, 0, c + k, 0, E⟩))
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨A + 3, 0, c + k, 0, E⟩ : Q) [fm]⊢ ⟨A + 2, 0, c + k, 1, E + 1⟩))
    apply stepStar_trans (ih (A + 2) c (E + 1)); ring_nf; finish

-- Inner loop: R5-R1-R2-R1x3 repeated k times
-- From (0, b+4k, c, 0, e+k) to (0, b, c+3k, 0, e)
-- Each round: R5, R1, R2, R1, R1, R1
theorem inner_loop : ∀ k b c e, ⟨(0 : ℕ), b + 4 * k, c, 0, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · simp; exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 4) c (e + 1))
    rw [show c + 3 * k = c + 3 * k from rfl]
    -- State: (0, b+4, c+3*k, 0, e+1)
    -- R5: e+1 matches e.succ
    rw [show e + 1 = e + 1 from rfl]
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨0, b + 4, c + 3 * k, 0, e + 1⟩ : Q) [fm]⊢ ⟨1, b + 4, c + 3 * k, 1, e⟩))
    -- R1: (1, b+4, ...) -> (0, b+3, c+3*k+1, 1, e)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨1, b + 4, c + 3 * k, 1, e⟩ : Q) [fm]⊢ ⟨0, b + 3, c + 3 * k + 1, 1, e⟩))
    -- R2: (0, b+3, (c+3*k)+1, 1, e) -> (3, b+3, c+3*k, 0, e)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨0, b + 3, c + 3 * k + 1, 1, e⟩ : Q) [fm]⊢ ⟨3, b + 3, c + 3 * k, 0, e⟩))
    -- R1: (3, b+3, ...) -> (2, b+2, c+3*k+1, 0, e)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨3, b + 3, c + 3 * k, 0, e⟩ : Q) [fm]⊢ ⟨2, b + 2, c + 3 * k + 1, 0, e⟩))
    -- R1: (2, b+2, ...) -> (1, b+1, c+3*k+2, 0, e)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨2, b + 2, c + 3 * k + 1, 0, e⟩ : Q) [fm]⊢ ⟨1, b + 1, c + 3 * k + 2, 0, e⟩))
    -- R1: (1, b+1, ...) -> (0, b, c+3*k+3, 0, e)
    apply stepStar_trans (step_stepStar
      (by simp [fm] : (⟨1, b + 1, c + 3 * k + 2, 0, e⟩ : Q) [fm]⊢ ⟨0, b, c + 3 * k + 3, 0, e⟩))
    rw [show c + 3 * k + 3 = c + 3 * (k + 1) from by ring]; finish

-- Exit for remainder 1: from (0,1,3m,0,F+1) to (0,0,0,6m+3,F+9m+3)
-- Steps: R5, R1, R2, R3, then R2-R3 chain, then R3 drain
theorem exit_r1 (m F : ℕ) :
    ⟨(0 : ℕ), 1, 3 * m, 0, F + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 0, 6 * m + 3, F + 9 * m + 3⟩ := by
  -- R5: (0, 1, 3m, 0, F+1) -> (1, 1, 3m, 1, F)
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 1, 3 * m, 0, F + 1⟩ : Q) [fm]⊢ ⟨1, 1, 3 * m, 1, F⟩)
  -- R1: (1, 1, 3m, 1, F) -> (0, 0, 3m+1, 1, F)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, 1, 3 * m, 1, F⟩ : Q) [fm]⊢ ⟨0, 0, 3 * m + 1, 1, F⟩))
  -- R2: (0, 0, 3m+1, 1, F) -> (3, 0, 3m, 0, F)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 0, 3 * m + 1, 1, F⟩ : Q) [fm]⊢ ⟨3, 0, 3 * m, 0, F⟩))
  -- R3: (3, 0, 3m, 0, F) -> (2, 0, 3m, 1, F+1)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨3, 0, 3 * m, 0, F⟩ : Q) [fm]⊢ ⟨2, 0, 3 * m, 1, F + 1⟩))
  -- R2-R3 chain: 3m rounds
  rw [show 3 * m = 0 + 3 * m from by ring]
  apply stepStar_trans (r2r3_chain (3 * m) 2 0 (F + 1))
  rw [show 2 + 2 * (3 * m) = 6 * m + 2 from by ring,
      show F + 1 + 3 * m = F + 3 * m + 1 from by ring]
  -- R3 drain
  apply stepStar_trans (r3_drain (6 * m + 2) 1 (F + 3 * m + 1))
  ring_nf; finish

-- Exit for remainder 3: from (0,3,3m,0,F+1) to (0,0,0,6m+5,F+9m+7)
-- Steps: R5, R1, R2, R1, R1, R3, then R2-R3 chain, then R3 drain
theorem exit_r3 (m F : ℕ) :
    ⟨(0 : ℕ), 3, 3 * m, 0, F + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 0, 6 * m + 5, F + 9 * m + 7⟩ := by
  -- R5: (0, 3, 3m, 0, F+1) -> (1, 3, 3m, 1, F)
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 3, 3 * m, 0, F + 1⟩ : Q) [fm]⊢ ⟨1, 3, 3 * m, 1, F⟩)
  -- R1: (1, 3, 3m, 1, F) -> (0, 2, 3m+1, 1, F)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, 3, 3 * m, 1, F⟩ : Q) [fm]⊢ ⟨0, 2, 3 * m + 1, 1, F⟩))
  -- R2: (0, 2, 3m+1, 1, F) -> (3, 2, 3m, 0, F)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨0, 2, 3 * m + 1, 1, F⟩ : Q) [fm]⊢ ⟨3, 2, 3 * m, 0, F⟩))
  -- R1: (3, 2, 3m, 0, F) -> (2, 1, 3m+1, 0, F)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨3, 2, 3 * m, 0, F⟩ : Q) [fm]⊢ ⟨2, 1, 3 * m + 1, 0, F⟩))
  -- R1: (2, 1, 3m+1, 0, F) -> (1, 0, 3m+2, 0, F)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨2, 1, 3 * m + 1, 0, F⟩ : Q) [fm]⊢ ⟨1, 0, 3 * m + 2, 0, F⟩))
  -- R3: (1, 0, 3m+2, 0, F) -> (0, 0, 3m+2, 1, F+1)
  apply stepStar_trans (step_stepStar
    (by simp [fm] : (⟨1, 0, 3 * m + 2, 0, F⟩ : Q) [fm]⊢ ⟨0, 0, 3 * m + 2, 1, F + 1⟩))
  -- R2-R3 chain: 3m+2 rounds
  rw [show 3 * m + 2 = 0 + (3 * m + 2) from by ring]
  apply stepStar_trans (r2r3_chain (3 * m + 2) 0 0 (F + 1))
  rw [show 0 + 2 * (3 * m + 2) = 6 * m + 4 from by ring,
      show F + 1 + (3 * m + 2) = F + 3 * m + 3 from by ring]
  -- R3 drain
  apply stepStar_trans (r3_drain (6 * m + 4) 1 (F + 3 * m + 3))
  ring_nf; finish

-- Main transition for D = 4m+1
theorem trans_mod1 (m F : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 1, F + m + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 6 * m + 3, F + 9 * m + 3⟩ := by
  rw [show (4 * m + 1 : ℕ) = 0 + (4 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (4 * m + 1) 0 0 (F + m + 1))
  rw [show (0 : ℕ) + (4 * m + 1) = 1 + 4 * m from by ring,
      show F + m + 1 = (F + 1) + m from by ring]
  apply stepStar_stepPlus_stepPlus (inner_loop m 1 0 (F + 1))
  rw [show 0 + 3 * m = 3 * m from by ring]
  exact exit_r1 m F

-- Main transition for D = 4m+3
theorem trans_mod3 (m F : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, 4 * m + 3, F + m + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 0, 6 * m + 5, F + 9 * m + 7⟩ := by
  rw [show (4 * m + 3 : ℕ) = 0 + (4 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (4 * m + 3) 0 0 (F + m + 1))
  rw [show (0 : ℕ) + (4 * m + 3) = 3 + 4 * m from by ring,
      show F + m + 1 = (F + 1) + m from by ring]
  apply stepStar_stepPlus_stepPlus (inner_loop m 3 0 (F + 1))
  rw [show 0 + 3 * m = 3 * m from by ring]
  exact exit_r3 m F

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ 1 ∧ D % 2 = 1 ∧ E ≥ D)
  · intro q ⟨D, E, hq, hD1, hDodd, hED⟩; subst hq
    have h4 : D % 4 = 1 ∨ D % 4 = 3 := by omega
    rcases h4 with h | h
    · obtain ⟨m, hm⟩ : ∃ m, D = 4 * m + 1 := ⟨D / 4, by omega⟩
      subst hm
      refine ⟨⟨0, 0, 0, 6 * m + 3, E + 8 * m + 2⟩,
        ⟨6 * m + 3, E + 8 * m + 2, rfl, by omega, by omega, by omega⟩, ?_⟩
      have h := trans_mod1 m (E - m - 1)
      rwa [show E - m - 1 + m + 1 = E from by omega,
           show E - m - 1 + 9 * m + 3 = E + 8 * m + 2 from by omega] at h
    · obtain ⟨m, hm⟩ : ∃ m, D = 4 * m + 3 := ⟨D / 4, by omega⟩
      subst hm
      refine ⟨⟨0, 0, 0, 6 * m + 5, E + 8 * m + 6⟩,
        ⟨6 * m + 5, E + 8 * m + 6, rfl, by omega, by omega, by omega⟩, ?_⟩
      have h := trans_mod3 m (E - m - 1)
      rwa [show E - m - 1 + m + 1 = E from by omega,
           show E - m - 1 + 9 * m + 7 = E + 8 * m + 6 from by omega] at h
  · exact ⟨1, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1262
