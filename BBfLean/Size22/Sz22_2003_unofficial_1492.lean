import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1492: [7/15, 9/14, 4/33, 55/2, 6/5]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  0
 2 -1  0  0 -1
-1  0  1  0  1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1492

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 drain: transfer a to c and e.
theorem r4_drain : ∀ k c e, ⟨a + k, (0 : ℕ), c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

-- R3 drain: transfer b and e to a (when c=0, d=0).
theorem r3_drain : ∀ k, ∀ a b e, ⟨a, b + k, (0 : ℕ), 0, e + k⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b e)
    ring_nf; finish

-- R3 drain specialized for b=0, e=0.
theorem r3_drain_full (k a : ℕ) :
    ⟨a, k, (0 : ℕ), 0, k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, 0⟩ := by
  have h := r3_drain k a 0 0
  simp at h; exact h

-- Opening: R5, R1, R2.
theorem opening (C E : ℕ) :
    ⟨0, (0 : ℕ), C + 2, 0, E⟩ [fm]⊢* ⟨0, 2, C, 0, E⟩ := by
  step fm; step fm; step fm; finish

-- R4 drain + opening combined (always at least 3 steps).
theorem r4_opening (N : ℕ) :
    ⟨N + 2, (0 : ℕ), 0, 0, 0⟩ [fm]⊢⁺ ⟨0, 2, N, 0, N + 2⟩ := by
  rw [show N + 2 = 0 + (N + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (N + 2) 0 0 (a := 0))
  rw [show (0 : ℕ) + (N + 2) = N + 2 from by ring]
  rw [show N + 2 = N + 1 + 1 from by ring]
  step fm; step fm; step fm; finish

-- Inner loop step: (0, 2, c+4, d, E) -> (0, 2, c, d+2, E) in 5 steps.
theorem inner_loop_step (C D E : ℕ) :
    ⟨0, (2 : ℕ), C + 4, D, E⟩ [fm]⊢* ⟨0, 2, C, D + 2, E⟩ := by
  rw [show C + 4 = (C + 2) + 2 from by ring]
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Inner loop: iterate the step k times.
theorem inner_loop : ∀ k C D E,
    ⟨0, (2 : ℕ), C + 4 * k, D, E⟩ [fm]⊢* ⟨0, 2, C, D + 2 * k, E⟩ := by
  intro k; induction k with
  | zero => intro C D E; simp; exists 0
  | succ k ih =>
    intro C D E
    rw [show C + 4 * (k + 1) = (C + 4 * k) + 4 from by ring]
    apply stepStar_trans (inner_loop_step (C + 4 * k) D E)
    apply stepStar_trans (ih C (D + 2) E)
    ring_nf; finish

-- Exit case c=1: (0, 2, 1, D, E+1) -> (2, 0, 0, D+1, E) in 2 steps.
theorem exit_c1 (D E : ℕ) :
    ⟨0, (2 : ℕ), 1, D, E + 1⟩ [fm]⊢* ⟨2, 0, 0, D + 1, E⟩ := by
  step fm; step fm; ring_nf; finish

-- Exit case c=3: (0, 2, 3, D, E+1) -> (2, 2, 0, D+1, E) in 5 steps.
theorem exit_c3 (D E : ℕ) :
    ⟨0, (2 : ℕ), 3, D, E + 1⟩ [fm]⊢* ⟨2, 2, 0, D + 1, E⟩ := by
  step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- R2R2R3 round: (2, B, 0, D+2, E+1) -> (2, B+3, 0, D, E) in 3 steps.
theorem r2r2r3_step (B D E : ℕ) :
    ⟨2, B, (0 : ℕ), D + 2, E + 1⟩ [fm]⊢* ⟨2, B + 3, 0, D, E⟩ := by
  rw [show D + 2 = D + 1 + 1 from by ring]
  step fm; step fm; step fm
  ring_nf; finish

-- R2R2R3 chain: iterate k times.
theorem r2r2r3_chain : ∀ k B D E,
    ⟨2, B, (0 : ℕ), D + 2 * k, E + k⟩ [fm]⊢* ⟨2, B + 3 * k, 0, D, E⟩ := by
  intro k; induction k with
  | zero => intro B D E; simp; exists 0
  | succ k ih =>
    intro B D E
    rw [show D + 2 * (k + 1) = (D + 2 * k) + 2 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    apply stepStar_trans (r2r2r3_step (B) (D + 2 * k) (E + k))
    apply stepStar_trans (ih (B + 3) D E)
    ring_nf; finish

-- R2 final: (2, B, 0, 1, E+1) -> (1, B+2, 0, 0, E+1) in 1 step.
theorem r2_final (B E : ℕ) :
    ⟨2, B, (0 : ℕ), 1, E + 1⟩ [fm]⊢* ⟨1, B + 2, 0, 0, E + 1⟩ := by
  step fm; ring_nf; finish

-- Odd case: n = 2j+1, canonical state is (4j+3, 0, 0, 0, 0).
theorem main_odd (j : ℕ) :
    ⟨4 * j + 3, (0 : ℕ), 0, 0, 0⟩ [fm]⊢⁺ ⟨6 * j + 5, 0, 0, 0, 0⟩ := by
  rw [show (4 * j + 3 : ℕ) = (4 * j + 1) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_opening (4 * j + 1))
  rw [show (4 * j + 1 + 2 : ℕ) = 4 * j + 3 from by ring,
      show (4 * j + 1 : ℕ) = 1 + 4 * j from by ring]
  apply stepStar_trans (inner_loop j 1 0 (4 * j + 3))
  rw [show (0 : ℕ) + 2 * j = 2 * j from by ring,
      show (4 * j + 3 : ℕ) = (4 * j + 2) + 1 from by ring]
  apply stepStar_trans (exit_c1 (2 * j) (4 * j + 2))
  rw [show (2 * j + 1 : ℕ) = 1 + 2 * j from by ring,
      show (4 * j + 2 : ℕ) = (3 * j + 2) + j from by ring]
  apply stepStar_trans (r2r2r3_chain j 0 1 (3 * j + 2))
  rw [show (0 : ℕ) + 3 * j = 3 * j from by ring,
      show (3 * j + 2 : ℕ) = (3 * j + 1) + 1 from by ring]
  apply stepStar_trans (r2_final (3 * j) (3 * j + 1))
  rw [show (3 * j + 1 + 1 : ℕ) = 3 * j + 2 from by ring]
  apply stepStar_trans (r3_drain_full (3 * j + 2) 1)
  ring_nf; finish

-- Even case: canonical state is (4j+5, 0, 0, 0, 0).
theorem main_even (j : ℕ) :
    ⟨4 * j + 5, (0 : ℕ), 0, 0, 0⟩ [fm]⊢⁺ ⟨6 * j + 9, 0, 0, 0, 0⟩ := by
  rw [show (4 * j + 5 : ℕ) = (4 * j + 3) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r4_opening (4 * j + 3))
  rw [show (4 * j + 3 + 2 : ℕ) = 4 * j + 5 from by ring,
      show (4 * j + 3 : ℕ) = 3 + 4 * j from by ring]
  apply stepStar_trans (inner_loop j 3 0 (4 * j + 5))
  rw [show (0 : ℕ) + 2 * j = 2 * j from by ring,
      show (4 * j + 5 : ℕ) = (4 * j + 4) + 1 from by ring]
  apply stepStar_trans (exit_c3 (2 * j) (4 * j + 4))
  rw [show (2 * j + 1 : ℕ) = 1 + 2 * j from by ring,
      show (4 * j + 4 : ℕ) = (3 * j + 4) + j from by ring]
  apply stepStar_trans (r2r2r3_chain j 2 1 (3 * j + 4))
  rw [show (2 : ℕ) + 3 * j = 3 * j + 2 from by ring,
      show (3 * j + 4 : ℕ) = (3 * j + 3) + 1 from by ring]
  apply stepStar_trans (r2_final (3 * j + 2) (3 * j + 3))
  rw [show (3 * j + 3 + 1 : ℕ) = 3 * j + 4 from by ring,
      show (3 * j + 2 + 2 : ℕ) = 3 * j + 4 from by ring]
  apply stepStar_trans (r3_drain_full (3 * j + 4) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨2 * n + 3, (0 : ℕ), 0, 0, 0⟩)
  · intro q ⟨n, hq⟩
    subst hq
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · subst hj
      rw [show 2 * (j + j) + 3 = 4 * j + 3 from by ring]
      refine ⟨⟨6 * j + 5, 0, 0, 0, 0⟩, ⟨3 * j + 1, ?_⟩, main_odd j⟩
      ring_nf
    · subst hj
      rw [show 2 * (2 * j + 1) + 3 = 4 * j + 5 from by ring]
      refine ⟨⟨6 * j + 9, 0, 0, 0, 0⟩, ⟨3 * j + 3, ?_⟩, main_even j⟩
      ring_nf
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_1492
