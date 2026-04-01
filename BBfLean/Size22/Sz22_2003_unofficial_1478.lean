import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1478: [7/15, 4/33, 9/14, 55/2, 6/5]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0 -1
-1  2  0 -1  0
-1  0  1  0  1
 1  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1478

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 chain: convert a to c and e.
theorem r4_chain : ∀ N, ⟨N, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + N, 0, e + N⟩ := by
  intro N; induction' N with N ih generalizing c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 1) (e := e + 1))
    ring_nf; finish

-- Spiral loop: each round consumes 4 from c, adds 2 to d.
-- (0, 0, c+4k, d, e) →* (0, 0, c, d+2k, e)
-- Each round: R5, R1, R3, R1, R1.
theorem spiral_loop : ∀ k, ⟨0, 0, c + 4 * k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show c + 4 * (k + 1) = (c + 4 * k) + 1 + 1 + 1 + 1 from by ring]
    step fm  -- R5: (1, 1, c+4k+2, d, e)
    step fm  -- R1: (1, 0, c+4k+1, d+1, e)
    step fm  -- R3: (0, 2, c+4k+1, d, e)
    step fm  -- R1: (0, 1, c+4k, d+1, e)
    step fm  -- R1: (0, 0, c+4k-1, d+2, e)
    apply stepStar_trans (ih (c := c) (d := d + 2) (e := e))
    ring_nf; finish

-- End case c=1: (0, 0, 1, d, e+1) ⊢⁺ (3, 0, 0, d, e).
theorem end_c1 : ⟨0, 0, 1, d, e + 1⟩ [fm]⊢⁺ ⟨3, 0, 0, d, e⟩ := by
  step fm  -- R5: (1, 1, 0, d, e+1)
  step fm  -- R2: (3, 0, 0, d, e)
  finish

-- End case c=3: (0, 0, 3, d, e+1) ⊢⁺ (2, 0, 0, d+1, e).
theorem end_c3 : ⟨0, 0, 3, d, e + 1⟩ [fm]⊢⁺ ⟨2, 0, 0, d + 1, e⟩ := by
  step fm  -- R5: (1, 1, 2, d, e+1)
  step fm  -- R1: (1, 0, 1, d+1, e+1)
  step fm  -- R3: (0, 2, 1, d, e+1)
  step fm  -- R1: (0, 1, 0, d+1, e+1)
  step fm  -- R2: (2, 0, 0, d+1, e)
  finish

-- Drain: R3, R2, R2 repeated.
theorem drain : ∀ k, ⟨a + 1, 0, 0, d + k, e + 2 * k⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm  -- R3: (a, 2, 0, d+k, e+2k+2)
    step fm  -- R2: (a+2, 1, 0, d+k, e+2k+1)
    step fm  -- R2: (a+4, 0, 0, d+k, e+2k)
    apply stepStar_trans (ih (a := a + 3) (d := d) (e := e))
    ring_nf; finish

-- Transition for N ≡ 1 (mod 4): (4q+1, 0, 0, 0, 0) ⊢⁺ (6q+3, 0, 0, 0, 0).
theorem trans_mod1 (q : ℕ) : ⟨4 * q + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨6 * q + 3, 0, 0, 0, 0⟩ := by
  -- R4 chain
  apply stepStar_stepPlus_stepPlus (r4_chain (4 * q + 1) (c := 0) (e := 0))
  simp only [Nat.zero_add]
  -- Spiral: q rounds
  rw [show (4 * q + 1 : ℕ) = 1 + 4 * q from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_loop q (c := 1) (d := 0) (e := 1 + 4 * q))
  simp only [Nat.zero_add]
  -- End c=1
  rw [show (1 + 4 * q : ℕ) = (4 * q) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (end_c1 (d := 2 * q) (e := 4 * q))
  -- Drain: 2q rounds
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show (2 * q : ℕ) = 0 + (2 * q) from by ring,
      show (4 * q : ℕ) = 0 + 2 * (2 * q) from by ring]
  apply stepStar_trans (drain (2 * q) (a := 2) (d := 0) (e := 0))
  ring_nf; finish

-- Transition for N ≡ 3 (mod 4): (4q+3, 0, 0, 0, 0) ⊢⁺ (6q+5, 0, 0, 0, 0).
theorem trans_mod3 (q : ℕ) : ⟨4 * q + 3, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨6 * q + 5, 0, 0, 0, 0⟩ := by
  -- R4 chain
  apply stepStar_stepPlus_stepPlus (r4_chain (4 * q + 3) (c := 0) (e := 0))
  simp only [Nat.zero_add]
  -- Spiral: q rounds
  rw [show (4 * q + 3 : ℕ) = 3 + 4 * q from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_loop q (c := 3) (d := 0) (e := 3 + 4 * q))
  simp only [Nat.zero_add]
  -- End c=3
  rw [show (3 + 4 * q : ℕ) = (4 * q + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (end_c3 (d := 2 * q) (e := 4 * q + 2))
  -- Drain: (2q+1) rounds
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (2 * q + 1 : ℕ) = 0 + (2 * q + 1) from by ring,
      show (4 * q + 2 : ℕ) = 0 + 2 * (2 * q + 1) from by ring]
  apply stepStar_trans (drain (2 * q + 1) (a := 1) (d := 0) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ N, q = ⟨N, 0, 0, 0, 0⟩ ∧ N ≥ 1 ∧ N % 2 = 1)
  · intro c ⟨N, hq, hN, hNodd⟩; subst hq
    have hmod : N % 4 = 1 ∨ N % 4 = 3 := by omega
    rcases hmod with h | h
    · obtain ⟨q, rfl⟩ : ∃ q, N = 4 * q + 1 := ⟨N / 4, by omega⟩
      exact ⟨⟨6 * q + 3, 0, 0, 0, 0⟩, ⟨6 * q + 3, rfl, by omega, by omega⟩, trans_mod1 q⟩
    · obtain ⟨q, rfl⟩ : ∃ q, N = 4 * q + 3 := ⟨N / 4, by omega⟩
      exact ⟨⟨6 * q + 5, 0, 0, 0, 0⟩, ⟨6 * q + 5, rfl, by omega, by omega⟩, trans_mod3 q⟩
  · exact ⟨1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1478
