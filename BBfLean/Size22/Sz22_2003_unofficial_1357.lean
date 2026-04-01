import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1357: [63/10, 4/33, 121/2, 5/7, 14/11]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1357

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3 drain: converts a to e (2 per a), with b=0, c=0.
theorem r3_drain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [Nat.add_succ a k]
    step fm
    apply stepStar_trans (ih (a := a) (e := e + 2))
    ring_nf; finish

-- R4 move: converts d to c, with a=0, b=0.
theorem r4_move : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (c := c + 1) (d := d))
    ring_nf; finish

-- R2 drain: drains b using e, with c=0.
theorem r2_drain : ∀ k, ⟨a, b + k, 0, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [Nat.add_succ b k, Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (a := a + 2) (b := b) (e := e))
    ring_nf; finish

-- Pair round (a=2): (R1, R1, R2) repeated k times.
theorem pair_round : ∀ k, ∀ b d e, ⟨2, b, 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 3 * k, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (d + 2) e)
    ring_nf; finish

-- Pair round (a=1): (R1, R2, R1) repeated k times.
theorem pair_round_a1 : ∀ k, ∀ b d e, ⟨1, b, 2 * k, d, e + k⟩ [fm]⊢* ⟨1, b + 3 * k, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) (d + 2) e)
    ring_nf; finish

-- Spiral for C = 2k+1 (odd C).
-- (0, 0, 2k+1, 0, e+4k+3) →* (6k+4, 0, 0, 2k+2, e)
theorem spiral_odd_c (k e : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, e + 4 * k + 3⟩ [fm]⊢* ⟨6 * k + 4, 0, 0, 2 * k + 2, e⟩ := by
  step fm; step fm; step fm
  rw [show e + 4 * k + 1 = e + 3 * k + 1 + k from by ring]
  apply stepStar_trans (pair_round k 1 2 (e + 3 * k + 1))
  rw [show 1 + 3 * k = 0 + (1 + 3 * k) from by ring,
      show e + 3 * k + 1 = e + (1 + 3 * k) from by ring]
  apply stepStar_trans (r2_drain (1 + 3 * k) (a := 2) (b := 0) (d := 2 + 2 * k) (e := e))
  ring_nf; finish

-- Spiral for C = 2k+2 (even C).
-- (0, 0, 2k+2, 0, e+4k+5) →* (6k+7, 0, 0, 2k+3, e)
theorem spiral_even_c (k e : ℕ) :
    ⟨0, 0, 2 * k + 2, 0, e + 4 * k + 5⟩ [fm]⊢* ⟨6 * k + 7, 0, 0, 2 * k + 3, e⟩ := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring,
      show e + 4 * k + 5 = e + 4 * k + 4 + 1 from by ring]
  step fm  -- R5
  rw [show e + 4 * k + 4 = e + 4 * k + 3 + 1 from by ring]
  step fm  -- R1
  step fm  -- R2
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm  -- R1
  rw [show e + 4 * k + 3 = e + 3 * k + 3 + k from by ring]
  apply stepStar_trans (pair_round_a1 k 3 3 (e + 3 * k + 3))
  rw [show 3 + 3 * k = 0 + (3 + 3 * k) from by ring,
      show e + 3 * k + 3 = e + (3 + 3 * k) from by ring]
  apply stepStar_trans (r2_drain (3 + 3 * k) (a := 1) (b := 0) (d := 3 + 2 * k) (e := e))
  ring_nf; finish

-- Full cycle: (3n+4, 0, 0, n+2, 2n^2+n) →* (3n+7, 0, 0, n+3, 2n^2+5n+3)
theorem full_cycle (n : ℕ) :
    ⟨3 * n + 4, 0, 0, n + 2, 2 * n ^ 2 + n⟩ [fm]⊢*
    ⟨3 * n + 7, 0, 0, n + 3, 2 * n ^ 2 + 5 * n + 3⟩ := by
  -- Phase 1: R3 drain a to e
  rw [show 3 * n + 4 = 0 + (3 * n + 4) from by ring]
  apply stepStar_trans (r3_drain (3 * n + 4) (a := 0) (d := n + 2) (e := 2 * n ^ 2 + n))
  -- Now at (0, 0, 0, n+2, 2n^2+7n+8)
  rw [show 2 * n ^ 2 + n + 2 * (3 * n + 4) = 2 * n ^ 2 + 7 * n + 8 from by ring,
      show (n + 2 : ℕ) = 0 + (n + 2) from by ring]
  -- Phase 2: R4 move d to c
  apply stepStar_trans (r4_move (n + 2) (c := 0) (d := 0) (e := 2 * n ^ 2 + 7 * n + 8))
  rw [show 0 + (n + 2) = n + 2 from by ring]
  -- Now at (0, 0, n+2, 0, 2n^2+7n+8). Apply spiral by parity.
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = 2k. C = n+2 = 2k+2.
    subst hk; rw [show k + k + 2 = 2 * k + 2 from by ring]
    rw [show 2 * (k + k) ^ 2 + 7 * (k + k) + 8 =
        (2 * (k + k) ^ 2 + 5 * (k + k) + 3) + 4 * k + 5 from by ring]
    apply stepStar_trans (spiral_even_c k (2 * (k + k) ^ 2 + 5 * (k + k) + 3))
    ring_nf; finish
  · -- n = 2k+1. C = n+2 = 2k+3.
    subst hk; rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 from by ring]
    rw [show 2 * (2 * k + 1) ^ 2 + 7 * (2 * k + 1) + 8 =
        (2 * (2 * k + 1) ^ 2 + 5 * (2 * k + 1) + 3) + 4 * (k + 1) + 3 from by ring]
    apply stepStar_trans (spiral_odd_c (k + 1) (2 * (2 * k + 1) ^ 2 + 5 * (2 * k + 1) + 3))
    ring_nf; finish

-- Main transition: ⊢⁺ version (the canonical state is never halted).
theorem main_trans (n : ℕ) :
    ⟨3 * n + 4, 0, 0, n + 2, 2 * n ^ 2 + n⟩ [fm]⊢⁺
    ⟨3 * (n + 1) + 4, 0, 0, (n + 1) + 2, 2 * (n + 1) ^ 2 + (n + 1)⟩ := by
  rw [show 3 * (n + 1) + 4 = 3 * n + 7 from by ring,
      show (n + 1) + 2 = n + 3 from by ring,
      show 2 * (n + 1) ^ 2 + (n + 1) = 2 * n ^ 2 + 5 * n + 3 from by ring]
  exact stepStar_stepPlus (full_cycle n) (by simp [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3 * 0 + 4, 0, 0, 0 + 2, 2 * 0 ^ 2 + 0⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n + 4, 0, 0, n + 2, 2 * n ^ 2 + n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
