import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #121: [1/405, 2/15, 63/2, 25/7, 3/5]

Vector representation:
```
 0 -4 -1  0
 1 -1 -1  0
-1  2  0  1
 0  0  2 -1
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_121

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+4, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k, ∀ c d,
    ⟨0, 0, c, d + k⟩ [fm]⊢* (⟨0, 0, c + 2 * k, d⟩ : Q) := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih _ _); ring_nf; finish

-- Interleave step: (j, 2, c+2, d) ->3 (j+1, 2, c, d+1)
theorem interleave_step : ∀ j c d,
    ⟨j, 2, c + 2, d⟩ [fm]⊢* (⟨j + 1, 2, c, d + 1⟩ : Q) := by
  intro j c d; step fm; step fm; step fm; ring_nf; finish

-- Interleave step generalized: (j, 2, 2k+1+2, d) ->* (j+1, 2, 2k+1, d+1)
-- Interleave iteration: (0, 2, 2k+1, d) ->* (k, 2, 1, d+k)
theorem interleave_iter : ∀ k, ∀ j d,
    ⟨j, 2, 2 * k + 1, d⟩ [fm]⊢* (⟨j + k, 2, 1, d + k⟩ : Q) := by
  intro k; induction' k with k ih <;> intro j d
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    apply stepStar_trans (interleave_step j _ _)
    apply stepStar_trans (ih (j + 1) (d + 1))
    ring_nf; finish

-- R3 chain: drain a into b and d
theorem a_drain : ∀ k, ∀ b d,
    ⟨k, b, 0, d⟩ [fm]⊢* (⟨0, b + 2 * k, 0, d + k⟩ : Q) := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm; apply stepStar_trans (ih _ _); ring_nf; finish

-- Iterated big reduction: (0, b+8k, 0, d+k) ->* (0, b, 0, d)
theorem big_reduce_iter : ∀ k, ∀ b d,
    ⟨0, b + 8 * k, 0, d + k⟩ [fm]⊢* (⟨0, b, 0, d⟩ : Q) := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show b + 8 * (k + 1) = (b + 8) + 8 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih _ _)
    step fm; step fm; step fm; ring_nf; finish

-- Common phase: (0, 0, 1, d+1) ->* (0, 2d+3, 0, 2d+2)
theorem common_phase : ∀ d,
    ⟨0, 0, 1, d + 1⟩ [fm]⊢* (⟨0, 2 * d + 3, 0, 2 * d + 2⟩ : Q) := by
  intro d
  -- d_to_c (d+1) steps: (0, 0, 1, d+1) ->* (0, 0, 2d+3, 0)
  apply stepStar_trans
  · have h := d_to_c (d + 1) 1 0
    rw [show (0 : ℕ) + (d + 1) = d + 1 from by ring,
        show 1 + 2 * (d + 1) = 2 * d + 3 from by ring] at h
    exact h
  -- start interleave: 3 steps to (0, 2, 2d+1, 1)
  step fm; step fm; step fm
  -- interleave_iter d steps: (0, 2, 2d+1, 1) ->* (0+d, 2, 1, 1+d)
  apply stepStar_trans
  · have h := interleave_iter d 0 1
    rw [show 0 + d = d from by ring, show 1 + d = d + 1 from by ring] at h
    exact h
  -- tail: R2 step: (d, 2, 1, d+1) -> (d+1, 1, 0, d+1)
  step fm
  -- a_drain: (d+1, 1, 0, d+1) -> (0, 2d+3, 0, 2d+2)
  apply stepStar_trans
  · have h := a_drain (d + 1) 1 (d + 1)
    rw [show 1 + 2 * (d + 1) = 2 * d + 3 from by ring,
        show d + 1 + (d + 1) = 2 * d + 2 from by ring] at h
    exact h
  finish

-- Terminal: (0, 3, 0, d+1) -> (0, 0, 1, d+2) in 16 steps
theorem term_3 : ∀ d,
    ⟨0, 3, 0, d + 1⟩ [fm]⊢* (⟨0, 0, 1, d + 2⟩ : Q) := by
  intro d; execute fm 16

-- Terminal: (0, 5, 0, d+1) -> (0, 0, 1, d+1) in 11 steps
theorem term_5 : ∀ d,
    ⟨0, 5, 0, d + 1⟩ [fm]⊢* (⟨0, 0, 1, d + 1⟩ : Q) := by
  intro d; execute fm 11

-- Terminal: (0, 7, 0, d+1) -> (0, 0, 1, d) in 6 steps
theorem term_7 : ∀ d,
    ⟨0, 7, 0, d + 1⟩ [fm]⊢* (⟨0, 0, 1, d⟩ : Q) := by
  intro d; execute fm 6

-- Terminal: (0, 1, 0, d+1) -> (0, 0, 1, d+3) in 21 steps
theorem term_1 : ∀ d,
    ⟨0, 1, 0, d + 1⟩ [fm]⊢* (⟨0, 0, 1, d + 3⟩ : Q) := by
  intro d; execute fm 21

-- Case d = 4k: (0, 0, 1, 4k+1) ⊢⁺ (0, 0, 1, 7k+3)
theorem case_0 (k : ℕ) :
    ⟨0, 0, 1, 4 * k + 1⟩ [fm]⊢⁺ (⟨0, 0, 1, 7 * k + 3⟩ : Q) := by
  apply stepStar_stepPlus_stepPlus
  · have h := common_phase (4 * k)
    rw [show 2 * (4 * k) + 3 = 8 * k + 3 from by ring,
        show 2 * (4 * k) + 2 = 8 * k + 2 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus
  · have h := big_reduce_iter k 3 (7 * k + 2)
    rw [show 3 + 8 * k = 8 * k + 3 from by ring,
        show 7 * k + 2 + k = 8 * k + 2 from by ring] at h
    exact h
  -- (0, 3, 0, 7k+2) -> (0, 0, 1, 7k+3) via term_3
  have h := term_3 (7 * k + 1)
  rw [show 7 * k + 1 + 1 = 7 * k + 2 from by ring,
      show 7 * k + 1 + 2 = 7 * k + 3 from by ring] at h
  exact stepStar_stepPlus h (by simp [Q])

-- Case d = 4k+1: (0, 0, 1, 4k+2) ⊢⁺ (0, 0, 1, 7k+4)
theorem case_1 (k : ℕ) :
    ⟨0, 0, 1, 4 * k + 2⟩ [fm]⊢⁺ (⟨0, 0, 1, 7 * k + 4⟩ : Q) := by
  apply stepStar_stepPlus_stepPlus
  · have h := common_phase (4 * k + 1)
    rw [show 2 * (4 * k + 1) + 3 = 8 * k + 5 from by ring,
        show 2 * (4 * k + 1) + 2 = 8 * k + 4 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus
  · have h := big_reduce_iter k 5 (7 * k + 4)
    rw [show 5 + 8 * k = 8 * k + 5 from by ring,
        show 7 * k + 4 + k = 8 * k + 4 from by ring] at h
    exact h
  have h := term_5 (7 * k + 3)
  rw [show 7 * k + 3 + 1 = 7 * k + 4 from by ring] at h
  exact stepStar_stepPlus h (by simp [Q])

-- Case d = 4k+2: (0, 0, 1, 4k+3) ⊢⁺ (0, 0, 1, 7k+5)
theorem case_2 (k : ℕ) :
    ⟨0, 0, 1, 4 * k + 3⟩ [fm]⊢⁺ (⟨0, 0, 1, 7 * k + 5⟩ : Q) := by
  apply stepStar_stepPlus_stepPlus
  · have h := common_phase (4 * k + 2)
    rw [show 2 * (4 * k + 2) + 3 = 8 * k + 7 from by ring,
        show 2 * (4 * k + 2) + 2 = 8 * k + 6 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus
  · have h := big_reduce_iter k 7 (7 * k + 6)
    rw [show 7 + 8 * k = 8 * k + 7 from by ring,
        show 7 * k + 6 + k = 8 * k + 6 from by ring] at h
    exact h
  have h := term_7 (7 * k + 5)
  rw [show 7 * k + 5 + 1 = 7 * k + 6 from by ring] at h
  exact stepStar_stepPlus h (by simp [Q])

-- Case d = 4k+3: (0, 0, 1, 4(k+1)) ⊢⁺ (0, 0, 1, 7k+9)
theorem case_3 (k : ℕ) :
    ⟨0, 0, 1, 4 * (k + 1)⟩ [fm]⊢⁺ (⟨0, 0, 1, 7 * k + 9⟩ : Q) := by
  apply stepStar_stepPlus_stepPlus
  · have h := common_phase (4 * k + 3)
    rw [show 4 * k + 3 + 1 = 4 * (k + 1) from by ring,
        show 2 * (4 * k + 3) + 3 = 8 * k + 9 from by ring,
        show 2 * (4 * k + 3) + 2 = 8 * k + 8 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus
  · have h := big_reduce_iter (k + 1) 1 (7 * k + 7)
    rw [show 1 + 8 * (k + 1) = 8 * k + 9 from by ring,
        show 7 * k + 7 + (k + 1) = 8 * k + 8 from by ring] at h
    exact h
  have h := term_1 (7 * k + 6)
  rw [show 7 * k + 6 + 1 = 7 * k + 7 from by ring,
      show 7 * k + 6 + 3 = 7 * k + 9 from by ring] at h
  exact stepStar_stepPlus h (by simp [Q])

-- Main transition: for any n, (0, 0, 1, n+1) steps to some (0, 0, 1, m+1)
theorem main_trans : ∀ n, ∃ m, ⟨0, 0, 1, n + 1⟩ [fm]⊢⁺ (⟨0, 0, 1, m + 1⟩ : Q) := by
  intro n
  match h : n % 4 with
  | 0 =>
    refine ⟨7 * (n / 4) + 2, ?_⟩
    have hn : n = 4 * (n / 4) := by omega
    rw [show n + 1 = 4 * (n / 4) + 1 from by omega,
        show 7 * (n / 4) + 2 + 1 = 7 * (n / 4) + 3 from by ring]
    exact case_0 (n / 4)
  | 1 =>
    refine ⟨7 * (n / 4) + 3, ?_⟩
    rw [show n + 1 = 4 * (n / 4) + 2 from by omega,
        show 7 * (n / 4) + 3 + 1 = 7 * (n / 4) + 4 from by ring]
    exact case_1 (n / 4)
  | 2 =>
    refine ⟨7 * (n / 4) + 4, ?_⟩
    rw [show n + 1 = 4 * (n / 4) + 3 from by omega,
        show 7 * (n / 4) + 4 + 1 = 7 * (n / 4) + 5 from by ring]
    exact case_2 (n / 4)
  | 3 =>
    refine ⟨7 * (n / 4) + 8, ?_⟩
    rw [show n + 1 = 4 * ((n / 4) + 1) from by omega,
        show 7 * (n / 4) + 8 + 1 = 7 * (n / 4) + 9 from by ring]
    exact case_3 (n / 4)
  | n + 4 => omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨0, 0, 1, 1⟩ : Q))
  · execute fm 8
  exact progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 1, n + 1⟩) 0 main_trans

end Sz22_2003_unofficial_121
