import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1796: [9/10, 49/2, 484/21, 5/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  2  0
 2 -1  0 -1  2
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1796

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_c : ∀ k, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

theorem r3r2r2_chain : ∀ k, ⟨0, b + k, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + 3 * k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b := b) (d := d + 3) (e := e + 2))
    ring_nf; finish

theorem r1r1r3_loop : ∀ k, ⟨2, b, 2 * (k + 1), d + k, e⟩ [fm]⊢* ⟨0, b + 3 * k + 4, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · step fm; step fm; finish
  · step fm; step fm
    rw [show b + 4 = (b + 3) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 3) (d := d) (e := e + 2))
    ring_nf; finish

theorem main_trans_pos : ⟨0, 0, 2 * (k + 1), 2 * k + g + 4, 0⟩ [fm]⊢⁺ ⟨0, 0, 8 * k + 10, 10 * k + g + 14, 0⟩ := by
  -- R5
  rw [show 2 * k + g + 4 = (2 * k + g + 3) + 1 from by ring]
  step fm
  -- R3: need d to have +1 pattern. After R5 we have d = 2k+g+3.
  -- For R3: b=1 >= 1 and d = 2k+g+3 = (2k+g+2)+1 >= 1. Need to rewrite.
  rw [show 2 * k + g + 3 = (k + g + 2) + k + 1 from by ring]
  step fm
  -- Now at (2, 0, 2*(k+1), (k+g+2)+k, 2). Need to show this matches r1r1r3_loop input.
  -- r1r1r3_loop k: (2, 0, 2*(k+1), d+k, 2) with d = k+g+2.
  -- (k+g+2)+k matches d+k. ✓
  apply stepStar_trans (r1r1r3_loop k (b := 0) (d := k + g + 2) (e := 2))
  -- Now at (0, 3k+4, 0, k+g+2, 2k+2)
  rw [show (0 : ℕ) + 3 * k + 4 = 0 + (3 * k + 4) from by ring,
      show k + g + 2 = (k + g + 1) + 1 from by ring,
      show 2 + 2 * k = 2 * k + 2 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * k + 4) (b := 0) (d := k + g + 1) (e := 2 * k + 2))
  rw [show k + g + 1 + 3 * (3 * k + 4) + 1 = 10 * k + g + 14 from by ring,
      show 2 * k + 2 + 2 * (3 * k + 4) = 0 + (8 * k + 10) from by ring]
  have := e_to_c (8 * k + 10) (c := 0) (d := 10 * k + g + 14) (e := 0)
  simp only [Nat.zero_add] at this ⊢; exact this

theorem main_trans_zero : ⟨0, 0, 0, g + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 2, g + 4, 0⟩ := by
  execute fm 6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, g⟩ ↦ ⟨0, 0, 2 * c, 2 * c + g + 2, 0⟩) ⟨0, 0⟩
  intro ⟨c, g⟩
  rcases c with _ | k
  · refine ⟨⟨1, g⟩, ?_⟩; dsimp only; simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]
    rw [show 2 + g + 2 = g + 4 from by ring]
    exact main_trans_zero
  · refine ⟨⟨4 * k + 5, 2 * k + g + 2⟩, ?_⟩; dsimp only
    rw [show 2 * (k + 1) + g + 2 = 2 * k + g + 4 from by ring,
        show 2 * (4 * k + 5) = 8 * k + 10 from by ring,
        show 8 * k + 10 + (2 * k + g + 2) + 2 = 10 * k + g + 14 from by ring]
    exact main_trans_pos
