import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #174: [1/45, 98/15, 3/7, 625/2, 3/5]

Vector representation:
```
 0 -2 -1  0
 1 -1 -1  2
 0  1  0 -1
-1  0  4  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_174

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+4, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R3 repeated: d → b
theorem d_to_b : ∀ k a b d, ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a, b+k, 0, d⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R1 repeated: subtracts 2 from b and 1 from c each step
theorem rule1_chain : ∀ k a b c d, ⟨a, b+2*k, c+k, d⟩ [fm]⊢* ⟨a, b, c, d⟩ := by
  intro k; induction k with
  | zero => intro a b c d; exists 0
  | succ k ih =>
    intro a b c d
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    exact ih a b c d

-- R4 repeated: a → c
theorem a_to_c : ∀ k a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+4*k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Climbing body: alternating R3+R2
-- (a, 0, c+k, d+1) ⊢* (a+k, 0, c, d+k+1)
theorem climb_body : ∀ k a c d, ⟨a, 0, c+k, d+1⟩ [fm]⊢* ⟨a+k, 0, c, d+k+1⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    rw [show (c + k) + 1 = c + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a+1) c (d+1))
    ring_nf; finish

-- Full phase 1: (0, 0, n+2, 0) ⊢* (n+1, n+2, 0, 0)
theorem phase1 (n : ℕ) : ⟨0, 0, n+2, 0⟩ [fm]⊢* ⟨n+1, n+2, 0, 0⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by ring]
  -- R5
  step fm
  -- R2
  rw [show n + 1 = n + 1 from rfl]
  step fm
  -- climb_body n 1 0 1
  apply stepStar_trans (c₂ := ⟨n+1, 0, 0, n+2⟩)
  · have h := climb_body n 1 0 1
    simp only [Nat.zero_add] at h
    rw [show 1 + n = n + 1 from by ring,
        show n + 1 + 1 = n + 2 from by ring] at h
    exact h
  -- d_to_b
  have h := d_to_b (n+2) (n+1) 0 0
  simp only [Nat.zero_add] at h; exact h

-- Big drain: R4 + 4×R1, removes 8 from b and 1 from a
theorem big_drain_step (a b : ℕ) : ⟨a+1, b+8, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  step fm
  rw [show b + 8 = (b + 6) + 2 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
  step fm
  rw [show b + 6 = (b + 4) + 2 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show b + 4 = (b + 2) + 2 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show b + 2 = b + 2 from rfl, show (1 : ℕ) = 0 + 1 from by ring]
  step fm; finish

-- Big drain chain
theorem big_drain : ∀ k a b, ⟨a+k, b+8*k, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 8 * (k + 1) = (b + 8 * k) + 8 from by ring]
    apply stepStar_trans (big_drain_step _ _)
    exact ih a b

-- Interleave: alternating R3, R2
-- (a, 0, c+k, d+k) ⊢* (a+k, 0, c, d+2*k)
theorem interleave : ∀ k a c d, ⟨a, 0, c+k, d+k⟩ [fm]⊢* ⟨a+k, 0, c, d+2*k⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show (c + k) + 1 = c + k + 1 from by ring]
    step fm
    rw [show d + k + 2 = d + 2 + k from by ring]
    apply stepStar_trans (ih (a+1) c (d+2))
    ring_nf; finish

-- Even b tails: (a+1, R, 0, 0) with R even ⊢⁺ (a', 0, c', 0)

-- R=0: R4 only
theorem even_tail_0 (a : ℕ) : ⟨a+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a, 0, 4, 0⟩ := by
  step fm; finish

-- R=2: R4 + 1×R1
theorem even_tail_2 (a : ℕ) : ⟨a+1, 2, 0, 0⟩ [fm]⊢⁺ ⟨a, 0, 3, 0⟩ := by
  step fm
  have h := rule1_chain 1 a 0 3 0
  rw [show 0 + 2 * 1 = 2 from by ring, show 3 + 1 = 4 from by ring] at h
  exact h

-- R=4: R4 + 2×R1. Use rule1_chain to handle the drain part.
theorem even_tail_4 (a : ℕ) : ⟨a+1, 4, 0, 0⟩ [fm]⊢⁺ ⟨a, 0, 2, 0⟩ := by
  -- R4: (a+1, 4, 0, 0) -> (a, 4, 4, 0)
  step fm
  -- Use rule1_chain 2 to go from (a, 4, 4, 0) = (a, 0+2*2, 2+2, 0) -> (a, 0, 2, 0)
  exact rule1_chain 2 a 0 2 0

-- R=6: R4 + 3×R1
theorem even_tail_6 (a : ℕ) : ⟨a+1, 6, 0, 0⟩ [fm]⊢⁺ ⟨a, 0, 1, 0⟩ := by
  step fm
  have h := rule1_chain 3 a 0 1 0
  rw [show 0 + 2 * 3 = 6 from by ring, show 1 + 3 = 4 from by ring] at h
  exact h

-- Odd b subcycle lemmas: (a+1, R, 0, 0) -> (a+delta, R', 0, 0) with R' even

-- b=7: (a+1, 7, 0, 0) ⊢* (a+1, 2, 0, 0)
-- R4 -> (a, 7, 4, 0) -> 3×R1 -> (a, 1, 1, 0) -> R2 -> (a+1, 0, 0, 2) -> d_to_b -> (a+1, 2, 0, 0)
theorem odd_7 (a : ℕ) : ⟨a+1, 7, 0, 0⟩ [fm]⊢* ⟨a+1, 2, 0, 0⟩ := by
  -- R4
  step fm
  -- (a, 7, 4, 0) -> 3×R1 -> (a, 1, 1, 0)
  apply stepStar_trans (c₂ := ⟨a, 1, 1, 0⟩)
  · have h := rule1_chain 3 a 1 1 0
    rw [show 1 + 2 * 3 = 7 from by ring, show 1 + 3 = 4 from by ring] at h
    exact h
  -- R2: (a, 1, 1, 0) = (a, 0+1, 0+1, 0) -> (a+1, 0, 0, 2)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- d_to_b 2
  have h := d_to_b 2 (a+1) 0 0
  simp only [Nat.zero_add] at h; exact h

-- b=3: (a+1, 3, 0, 0) ⊢* (a+3, 4, 0, 0)
-- R4 -> (a, 3, 4, 0) -> R1 -> (a, 1, 3, 0) -> R2 -> (a+1, 0, 2, 2)
-- -> interleave 2 -> (a+3, 0, 0, 4) -> d_to_b 4 -> (a+3, 4, 0, 0)
theorem odd_3 (a : ℕ) : ⟨a+1, 3, 0, 0⟩ [fm]⊢* ⟨a+3, 4, 0, 0⟩ := by
  -- R4
  step fm
  -- (a, 3, 4, 0) -> 1×R1 -> (a, 1, 3, 0)
  apply stepStar_trans (c₂ := ⟨a, 1, 3, 0⟩)
  · have h := rule1_chain 1 a 1 3 0
    rw [show 1 + 2 * 1 = 3 from by ring, show 3 + 1 = 4 from by ring] at h
    exact h
  -- R2: (a, 0+1, 2+1, 0) -> (a+1, 0, 2, 2)
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  -- interleave 2: (a+1, 0, 2, 2) -> (a+3, 0, 0, 4)
  apply stepStar_trans (c₂ := ⟨a+3, 0, 0, 4⟩)
  · have h := interleave 2 (a+1) 0 0
    simp only [Nat.zero_add] at h
    rw [show a + 1 + 2 = a + 3 from by ring] at h
    convert h using 2
  -- d_to_b 4
  have h := d_to_b 4 (a+3) 0 0
  simp only [Nat.zero_add] at h; exact h

-- b=5: (a+1, 5, 0, 0) ⊢* (a+2, 3, 0, 0)
-- R4 -> (a, 5, 4, 0) -> 2×R1 -> (a, 1, 2, 0) -> R2 -> (a+1, 0, 1, 2)
-- -> interleave 1 -> (a+2, 0, 0, 3) -> d_to_b -> (a+2, 3, 0, 0)
theorem odd_5 (a : ℕ) : ⟨a+1, 5, 0, 0⟩ [fm]⊢* ⟨a+2, 3, 0, 0⟩ := by
  -- R4
  step fm
  -- (a, 5, 4, 0) -> 2×R1 -> (a, 1, 2, 0)
  apply stepStar_trans (c₂ := ⟨a, 1, 2, 0⟩)
  · have h := rule1_chain 2 a 1 2 0
    rw [show 1 + 2 * 2 = 5 from by ring, show 2 + 2 = 4 from by ring] at h
    exact h
  -- R2: (a, 0+1, 1+1, 0) -> (a+1, 0, 1, 2)
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  -- interleave 1: (a+1, 0, 1, 2) -> (a+2, 0, 0, 3)
  apply stepStar_trans (c₂ := ⟨a+2, 0, 0, 3⟩)
  · have h := interleave 1 (a+1) 0 1
    simp only [Nat.zero_add] at h
    rw [show a + 1 + 1 = a + 2 from by ring, show 1 + 2 * 1 = 3 from by ring] at h
    exact h
  -- d_to_b 3
  have h := d_to_b 3 (a+2) 0 0
  simp only [Nat.zero_add] at h; exact h

-- b=1: (a+1, 1, 0, 0) ⊢* (a+4, 5, 0, 0)
-- R4 -> (a, 1, 4, 0) -> R2 -> (a+1, 0, 3, 2)
-- -> interleave 2 (a+1) 1 0 -> (a+3, 0, 1, 4)
-- -> interleave 1 (a+3) 0 3 -> (a+4, 0, 0, 5) -> d_to_b -> (a+4, 5, 0, 0)
theorem odd_1 (a : ℕ) : ⟨a+1, 1, 0, 0⟩ [fm]⊢* ⟨a+4, 5, 0, 0⟩ := by
  -- R4: (a, 1, 4, 0)
  step fm
  -- R2: (a, 0+1, 3+1, 0) -> (a+1, 0, 3, 2)
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
  step fm
  -- interleave 2: (a+1, 0, 3, 2) -> (a+3, 0, 1, 4)
  apply stepStar_trans (c₂ := ⟨a+3, 0, 1, 4⟩)
  · have h := interleave 2 (a+1) 1 0
    simp only [Nat.zero_add] at h
    rw [show a + 1 + 2 = a + 3 from by ring] at h
    exact h
  -- interleave 1: (a+3, 0, 1, 4) -> (a+4, 0, 0, 5)
  apply stepStar_trans (c₂ := ⟨a+4, 0, 0, 5⟩)
  · have h := interleave 1 (a+3) 0 3
    simp only [Nat.zero_add] at h
    rw [show a + 3 + 1 = a + 4 from by ring] at h
    exact h
  -- d_to_b 5
  have h := d_to_b 5 (a+4) 0 0
  simp only [Nat.zero_add] at h; exact h

-- Odd chain: resolve any odd b to even b
-- b=1 -> b=5 -> b=3 -> b=4 (even)
theorem odd_chain_1 (a : ℕ) : ⟨a+1, 1, 0, 0⟩ [fm]⊢* ⟨a+7, 4, 0, 0⟩ := by
  apply stepStar_trans (odd_1 a)
  rw [show a + 4 = (a + 3) + 1 from by ring]
  apply stepStar_trans (odd_5 (a+3))
  rw [show a + 3 + 2 = (a + 4) + 1 from by ring]
  apply stepStar_trans (odd_3 (a+4))
  ring_nf; finish

-- b=5 -> b=3 -> b=4
theorem odd_chain_5 (a : ℕ) : ⟨a+1, 5, 0, 0⟩ [fm]⊢* ⟨a+4, 4, 0, 0⟩ := by
  apply stepStar_trans (odd_5 a)
  rw [show a + 2 = (a + 1) + 1 from by ring]
  apply stepStar_trans (odd_3 (a+1))
  ring_nf; finish

-- Main transition: for each C mod 8 case
-- We prove: (C-1, C, 0, 0) ⊢⁺ (a', 0, c', 0) with a'+c' >= 2.
-- This uses big_drain + odd/even tails.

-- Case C mod 8 = 0, C = 8*(q+1), q >= 0:
-- (8q+7, 8q+8, 0, 0) -> big_drain (q+1) -> (7q+6, 0, 0, 0)
-- -> even_tail_0 -> (7q+5, 0, 4, 0). a'+c' = 7q+9 >= 9.
theorem trans_mod0 (q : ℕ) :
    ⟨8*q+7, 8*(q+1), 0, 0⟩ [fm]⊢⁺ ⟨7*q+5, 0, 4, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+6, 0, 0, 0⟩)
  · have h := big_drain (q+1) (7*q+6) 0
    rw [show 7 * q + 6 + (q + 1) = 8 * q + 7 from by ring,
        show 0 + 8 * (q + 1) = 8 * (q + 1) from by ring] at h
    exact h
  rw [show 7 * q + 6 = (7 * q + 5) + 1 from by ring]
  exact even_tail_0 (7*q+5)

-- Case C mod 8 = 2, C = 8*q+2, q >= 0:
-- (8q+1, 8q+2, 0, 0) -> big_drain q -> (7q+1, 2, 0, 0)
-- -> even_tail_2 -> (7q, 0, 3, 0). a'+c' = 7q+3 >= 3.
theorem trans_mod2 (q : ℕ) :
    ⟨8*q+1, 8*q+2, 0, 0⟩ [fm]⊢⁺ ⟨7*q, 0, 3, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+1, 2, 0, 0⟩)
  · have h := big_drain q (7*q+1) 2
    rw [show 7 * q + 1 + q = 8 * q + 1 from by ring,
        show 2 + 8 * q = 8 * q + 2 from by ring] at h
    exact h
  rw [show 7 * q + 1 = (7 * q) + 1 from by ring]
  exact even_tail_2 (7*q)

-- Case C mod 8 = 4, C = 8*q+4, q >= 0:
-- (8q+3, 8q+4, 0, 0) -> big_drain q -> (7q+3, 4, 0, 0)
-- -> even_tail_4 -> (7q+2, 0, 2, 0). a'+c' = 7q+4 >= 4.
theorem trans_mod4 (q : ℕ) :
    ⟨8*q+3, 8*q+4, 0, 0⟩ [fm]⊢⁺ ⟨7*q+2, 0, 2, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+3, 4, 0, 0⟩)
  · have h := big_drain q (7*q+3) 4
    rw [show 7 * q + 3 + q = 8 * q + 3 from by ring,
        show 4 + 8 * q = 8 * q + 4 from by ring] at h
    exact h
  rw [show 7 * q + 3 = (7 * q + 2) + 1 from by ring]
  exact even_tail_4 (7*q+2)

-- Case C mod 8 = 6, C = 8*q+6, q >= 0:
-- (8q+5, 8q+6, 0, 0) -> big_drain q -> (7q+5, 6, 0, 0)
-- -> even_tail_6 -> (7q+4, 0, 1, 0). a'+c' = 7q+5 >= 5.
theorem trans_mod6 (q : ℕ) :
    ⟨8*q+5, 8*q+6, 0, 0⟩ [fm]⊢⁺ ⟨7*q+4, 0, 1, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+5, 6, 0, 0⟩)
  · have h := big_drain q (7*q+5) 6
    rw [show 7 * q + 5 + q = 8 * q + 5 from by ring,
        show 6 + 8 * q = 8 * q + 6 from by ring] at h
    exact h
  rw [show 7 * q + 5 = (7 * q + 4) + 1 from by ring]
  exact even_tail_6 (7*q+4)

-- Case C mod 8 = 1, C = 8*(q+1)+1 = 8q+9, q >= 0:
-- (8q+8, 8q+9, 0, 0) -> big_drain (q+1) -> (7q+7, 1, 0, 0)
-- -> odd_chain_1 -> (7q+13, 4, 0, 0) -> even_tail_4 -> (7q+12, 0, 2, 0).
-- But wait: big_drain needs a=(7q+7), b=1, k=q+1: (7q+7+q+1, 1+8*(q+1), 0, 0) = (8q+8, 8q+9, 0, 0). ✓
-- odd_chain_1: (7q+7, 1, 0, 0) = ((7q+6)+1, 1, 0, 0) ⊢* ((7q+6)+7, 4, 0, 0) = (7q+13, 4, 0, 0).
-- even_tail_4: ((7q+12)+1, 4, 0, 0) ⊢⁺ (7q+12, 0, 2, 0).
-- But 7q+13 = (7q+12)+1. ✓
theorem trans_mod1 (q : ℕ) :
    ⟨8*q+8, 8*q+9, 0, 0⟩ [fm]⊢⁺ ⟨7*q+12, 0, 2, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+7, 1, 0, 0⟩)
  · have h := big_drain (q+1) (7*q+7) 1
    rw [show 7 * q + 7 + (q + 1) = 8 * q + 8 from by ring,
        show 1 + 8 * (q + 1) = 8 * q + 9 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+13, 4, 0, 0⟩)
  · rw [show 7 * q + 7 = (7 * q + 6) + 1 from by ring]
    apply stepStar_trans (odd_chain_1 (7*q+6))
    ring_nf; finish
  rw [show 7 * q + 13 = (7 * q + 12) + 1 from by ring]
  exact even_tail_4 (7*q+12)

-- Case C mod 8 = 3, C = 8*q+3, q >= 0:
-- (8q+2, 8q+3, 0, 0) -> big_drain q -> (7q+2, 3, 0, 0)
-- -> odd_3 -> (7q+4, 4, 0, 0) -> even_tail_4 -> (7q+3, 0, 2, 0).
-- odd_3: ((7q+1)+1, 3, 0, 0) ⊢* ((7q+1)+3, 4, 0, 0) = (7q+4, 4, 0, 0). ✓
theorem trans_mod3 (q : ℕ) :
    ⟨8*q+2, 8*q+3, 0, 0⟩ [fm]⊢⁺ ⟨7*q+3, 0, 2, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+2, 3, 0, 0⟩)
  · have h := big_drain q (7*q+2) 3
    rw [show 7 * q + 2 + q = 8 * q + 2 from by ring,
        show 3 + 8 * q = 8 * q + 3 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+4, 4, 0, 0⟩)
  · rw [show 7 * q + 2 = (7 * q + 1) + 1 from by ring]
    apply stepStar_trans (odd_3 (7*q+1))
    ring_nf; finish
  rw [show 7 * q + 4 = (7 * q + 3) + 1 from by ring]
  exact even_tail_4 (7*q+3)

-- Case C mod 8 = 5, C = 8*q+5, q >= 0:
-- (8q+4, 8q+5, 0, 0) -> big_drain q -> (7q+4, 5, 0, 0)
-- -> odd_chain_5 -> (7q+7, 4, 0, 0) -> even_tail_4 -> (7q+6, 0, 2, 0).
-- odd_chain_5: ((7q+3)+1, 5, 0, 0) ⊢* ((7q+3)+4, 4, 0, 0) = (7q+7, 4, 0, 0). ✓
theorem trans_mod5 (q : ℕ) :
    ⟨8*q+4, 8*q+5, 0, 0⟩ [fm]⊢⁺ ⟨7*q+6, 0, 2, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+4, 5, 0, 0⟩)
  · have h := big_drain q (7*q+4) 5
    rw [show 7 * q + 4 + q = 8 * q + 4 from by ring,
        show 5 + 8 * q = 8 * q + 5 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+7, 4, 0, 0⟩)
  · rw [show 7 * q + 4 = (7 * q + 3) + 1 from by ring]
    apply stepStar_trans (odd_chain_5 (7*q+3))
    ring_nf; finish
  rw [show 7 * q + 7 = (7 * q + 6) + 1 from by ring]
  exact even_tail_4 (7*q+6)

-- Case C mod 8 = 7, C = 8*q+7, q >= 0:
-- (8q+6, 8q+7, 0, 0) -> big_drain q -> (7q+6, 7, 0, 0)
-- -> odd_7 -> (7q+6, 2, 0, 0) -> even_tail_2 -> (7q+5, 0, 3, 0).
-- odd_7: ((7q+5)+1, 7, 0, 0) ⊢* ((7q+5)+1, 2, 0, 0) = (7q+6, 2, 0, 0). ✓
theorem trans_mod7 (q : ℕ) :
    ⟨8*q+6, 8*q+7, 0, 0⟩ [fm]⊢⁺ ⟨7*q+5, 0, 3, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+6, 7, 0, 0⟩)
  · have h := big_drain q (7*q+6) 7
    rw [show 7 * q + 6 + q = 8 * q + 6 from by ring,
        show 7 + 8 * q = 8 * q + 7 from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨7*q+6, 2, 0, 0⟩)
  · rw [show 7 * q + 6 = (7 * q + 5) + 1 from by ring]
    exact odd_7 (7*q+5)
  rw [show 7 * q + 6 = (7 * q + 5) + 1 from by ring]
  exact even_tail_2 (7*q+5)

-- Combined main transition
theorem main_trans (n : ℕ) :
    ∃ a' c', a' + c' ≥ 2 ∧ ⟨n+1, n+2, 0, 0⟩ [fm]⊢⁺ ⟨a', 0, c', 0⟩ := by
  have hmod := Nat.div_add_mod (n+2) 8
  set q := (n+2) / 8
  set r := (n+2) % 8
  have hr : r < 8 := Nat.mod_lt (n+2) (by omega)
  interval_cases r
  · -- r = 0, n+2 = 8q, n = 8q-2, need q >= 1 since n >= 0 means 8q >= 2
    rw [show n + 1 = 8 * q - 1 from by omega, show n + 2 = 8 * (q - 1 + 1) from by omega]
    rcases q with _ | q'
    · omega
    · rw [show q' + 1 - 1 + 1 = q' + 1 from by omega,
          show 8 * (q' + 1) - 1 = 8 * q' + 7 from by omega]
      exact ⟨7*q'+5, 4, by omega, trans_mod0 q'⟩
  · -- r = 1, n+2 = 8q+1, need q >= 1
    rw [show n + 1 = 8 * q from by omega, show n + 2 = 8 * q + 1 from by omega]
    rcases q with _ | q'
    · omega
    · rw [show 8 * (q' + 1) = 8 * q' + 8 from by ring,
          show 8 * q' + 8 + 1 = 8 * q' + 9 from by ring]
      exact ⟨7*q'+12, 2, by omega, trans_mod1 q'⟩
  · -- r = 2, n+2 = 8q+2
    rw [show n + 1 = 8 * q + 1 from by omega, show n + 2 = 8 * q + 2 from by omega]
    exact ⟨7*q, 3, by omega, trans_mod2 q⟩
  · -- r = 3, n+2 = 8q+3
    rw [show n + 1 = 8 * q + 2 from by omega, show n + 2 = 8 * q + 3 from by omega]
    exact ⟨7*q+3, 2, by omega, trans_mod3 q⟩
  · -- r = 4, n+2 = 8q+4
    rw [show n + 1 = 8 * q + 3 from by omega, show n + 2 = 8 * q + 4 from by omega]
    exact ⟨7*q+2, 2, by omega, trans_mod4 q⟩
  · -- r = 5, n+2 = 8q+5
    rw [show n + 1 = 8 * q + 4 from by omega, show n + 2 = 8 * q + 5 from by omega]
    exact ⟨7*q+6, 2, by omega, trans_mod5 q⟩
  · -- r = 6, n+2 = 8q+6
    rw [show n + 1 = 8 * q + 5 from by omega, show n + 2 = 8 * q + 6 from by omega]
    exact ⟨7*q+4, 1, by omega, trans_mod6 q⟩
  · -- r = 7, n+2 = 8q+7
    rw [show n + 1 = 8 * q + 6 from by omega, show n + 2 = 8 * q + 7 from by omega]
    exact ⟨7*q+5, 3, by omega, trans_mod7 q⟩

-- Full cycle: (0, 0, n+2, 0) ⊢⁺ (a', 0, c', 0) with a'+c' >= 2
theorem full_cycle (n : ℕ) :
    ∃ a' c', a' + c' ≥ 2 ∧ ⟨0, 0, n+2, 0⟩ [fm]⊢⁺ ⟨a', 0, c', 0⟩ := by
  obtain ⟨a', c', hge, htrans⟩ := main_trans n
  exact ⟨a', c', hge, stepStar_stepPlus_stepPlus (phase1 n) htrans⟩

-- Progress from any (a, 0, c, 0) with a+c >= 2
theorem progress (a c : ℕ) (h : a + c ≥ 2) :
    ∃ a' c', a' + c' ≥ 2 ∧ ⟨a, 0, c, 0⟩ [fm]⊢⁺ ⟨a', 0, c', 0⟩ := by
  rcases a with _ | a
  · -- a = 0, c >= 2
    rw [show c = (c - 2) + 2 from by omega]
    exact full_cycle (c - 2)
  · -- a >= 1
    rw [show a + 1 = a + 1 from rfl]
    refine ⟨a, c + 4, by omega, ?_⟩
    step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c, 0⟩ ∧ a + c ≥ 2)
  · intro q ⟨a, c, hq, hge⟩
    subst hq
    obtain ⟨a', c', hge', htrans⟩ := progress a c hge
    exact ⟨⟨a', 0, c', 0⟩, ⟨a', c', rfl, hge'⟩, htrans⟩
  · exact ⟨0, 4, rfl, by omega⟩

end Sz22_2003_unofficial_174
