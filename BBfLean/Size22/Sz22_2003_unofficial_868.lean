import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #868: [4/105, 5/6, 539/2, 3/7, 14/11]

Vector representation:
```
 2 -1 -1 -1  0
-1 -1  1  0  0
-1  0  0  2  1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_868

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem round_c0 : ⟨0, b + 4, 0, 0, e + 1⟩ [fm]⊢* ⟨0, b, 2, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem round_cS : ⟨0, b + 4, c + 1, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem round : ⟨0, b + 4, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 2, 0, e⟩ := by
  rcases c with _ | c
  · exact round_c0
  · rw [show c + 1 + 2 = c + 3 from by ring]; exact round_cS

theorem rounds_chain : ∀ k, ⟨0, 4 * k + b, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · ring_nf; finish
  · rw [show 4 * (k + 1) + b = 4 * k + (b + 4) from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 4) (c := c) (e := e + 1))
    apply stepStar_trans (round (b := b) (c := c + 2 * k) (e := e))
    rw [show c + 2 * k + 2 = c + 2 * (k + 1) from by ring]; finish

theorem b0_exit : ⟨0, 0, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, c, 3, e + 1⟩ := by
  step fm; step fm; finish

theorem tail_one : ⟨0, 0, c + 1, d + 2, e⟩ [fm]⊢* ⟨0, 0, c, d + 4, e + 2⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem tail_chain : ∀ k, ⟨0, 0, k, d + 2, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 + 2 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · ring_nf; finish
  · rw [show k + 1 = k + 1 from rfl]
    apply stepStar_trans (tail_one (c := k) (d := d) (e := e))
    apply stepStar_trans (ih (d := d + 2) (e := e + 2))
    rw [show d + 2 + 2 + 2 * k = d + 2 + 2 * (k + 1) from by ring,
        show e + 2 + 2 * k = e + 2 * (k + 1) from by ring]; finish

theorem b3_exit_c0 : ⟨0, 3, 0, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 1, 2, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem b3_exit_cS : ⟨0, 3, c + 1, 0, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2, 2, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem b3_exit : ⟨0, 3, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, c + 1, 2, e + 1⟩ := by
  rcases c with _ | c
  · exact b3_exit_c0
  · rw [show c + 1 + 1 = c + 2 from by ring]; exact b3_exit_cS

theorem main_trans (K E : ℕ) :
    ⟨0, 0, 0, 4 * (K + 1), E + K + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * (K + 2), E + 7 * K + 10⟩ := by
  -- First R4 step to get ⊢⁺
  rw [show 4 * (K + 1) = (4 * K + 3) + 1 from by ring]
  step fm
  -- After first R4 step: (0, 1, 0, 4*K+3, E+K+2)
  -- d_to_b for remaining steps
  rw [show (4 * K + 3 : ℕ) = 0 + (4 * K + 3) from by ring]
  apply stepStar_trans (d_to_b (4 * K + 3) (b := 1) (d := 0) (e := E + K + 2))
  -- Now at (0, 4*(K+1), 0, 0, E+K+2)
  rw [show 1 + (4 * K + 3) = 4 * (K + 1) + 0 from by ring,
      show E + K + 2 = (E + 1) + (K + 1) from by ring]
  apply stepStar_trans (rounds_chain (K + 1) (b := 0) (c := 0) (e := E + 1))
  -- Now at (0, 0, 2*(K+1), 0, E+1)
  rw [show 0 + 2 * (K + 1) = 2 * (K + 1) from by ring]
  apply stepStar_trans (b0_exit (c := 2 * (K + 1)) (e := E))
  -- Now at (0, 0, 2*(K+1), 3, E+1)
  -- tail_chain: (0, 0, 2*(K+1), 3, E+1) -> (0, 0, 0, 3+4*(K+1), E+1+4*(K+1))
  rw [show (2 * (K + 1) : ℕ) = 2 * (K + 1) from rfl,
      show (3 : ℕ) = 1 + 2 from by ring]
  apply stepStar_trans (tail_chain (2 * (K + 1)) (d := 1) (e := E + 1))
  -- Now at (0, 0, 0, 1+2+4*(K+1), E+1+4*(K+1))
  rw [show 1 + 2 + 2 * (2 * (K + 1)) = 0 + (4 * K + 7) from by ring,
      show E + 1 + 2 * (2 * (K + 1)) = E + 4 * K + 5 from by ring]
  -- d_to_b
  apply stepStar_trans (d_to_b (4 * K + 7) (b := 0) (d := 0) (e := E + 4 * K + 5))
  rw [show 0 + (4 * K + 7) = 4 * (K + 1) + 3 from by ring,
      show E + 4 * K + 5 = (E + 3 * K + 4) + (K + 1) from by ring]
  -- Rounds (K+1) with b=3
  apply stepStar_trans (rounds_chain (K + 1) (b := 3) (c := 0) (e := E + 3 * K + 4))
  rw [show 0 + 2 * (K + 1) = 2 * (K + 1) from by ring,
      show E + 3 * K + 4 = (E + 3 * K + 3) + 1 from by ring]
  -- b3_exit
  apply stepStar_trans (b3_exit (c := 2 * (K + 1)) (e := E + 3 * K + 3))
  -- tail_chain
  rw [show 2 * (K + 1) + 1 = 2 * K + 3 from by ring,
      show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (tail_chain (2 * K + 3) (d := 0) (e := E + 3 * K + 3 + 1))
  rw [show 0 + 2 + 2 * (2 * K + 3) = 4 * (K + 2) from by ring,
      show E + 3 * K + 3 + 1 + 2 * (2 * K + 3) = E + 7 * K + 10 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨K, E⟩ ↦ ⟨0, 0, 0, 4 * (K + 1), E + K + 2⟩) ⟨0, 0⟩
  intro ⟨K, E⟩; exact ⟨⟨K + 1, E + 6 * K + 7⟩, by
    show ⟨0, 0, 0, 4 * (K + 1), E + K + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * ((K + 1) + 1), (E + 6 * K + 7) + (K + 1) + 2⟩
    rw [show (E + 6 * K + 7) + (K + 1) + 2 = E + 7 * K + 10 from by ring]
    exact main_trans K E⟩
