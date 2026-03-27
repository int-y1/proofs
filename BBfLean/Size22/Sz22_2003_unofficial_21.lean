import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #21: [1/135, 98/15, 3/7, 125/2, 7/5]

Vector representation:
```
 0 -3 -1  0
 1 -1 -1  2
 0  1  0 -1
-1  0  3  0
 0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_21

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+3, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- Interleaved R3/R2 chain
theorem interleaved : ∀ j, ∀ a d, ⟨a, 0, j+1, d+1⟩ [fm]⊢* ⟨a+j+1, 0, 0, d+j+2⟩ := by
  intro j; induction' j with j ih <;> intro a d
  · step fm; step fm; finish
  · rw [show (j + 1) + 1 = j + 2 from by ring]
    step fm; step fm
    have h := ih (a + 1) (d + 1)
    rw [show a + 1 + j + 1 = a + (j + 1) + 1 from by ring,
        show d + 1 + j + 2 = d + (j + 1) + 2 from by ring] at h
    exact h

-- R3 transfer: d → b
theorem d_to_b : ∀ k, ∀ a b d, ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a, b+k, 0, d⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: a → c
theorem a_to_c : ∀ k, ∀ a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+3*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R1 chain
theorem r1_chain : ∀ k, ∀ a b c d, ⟨a, b+3*k, c+k, d⟩ [fm]⊢* ⟨a, b, c, d⟩ := by
  intro k; induction' k with k ih <;> intro a b c d
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
      show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  exact ih _ _ _ _

-- B≥9 one step: (a+1, b+9, 3, 0) → (a, b, 3, 0)
theorem b9_step (a b : ℕ) : ⟨a+1, b+9, 3, 0⟩ [fm]⊢* ⟨a, b, 3, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨a+1, b, 0, 0⟩)
  · have h := r1_chain 3 (a+1) b 0 0
    rw [show b + 3 * 3 = b + 9 from by ring, show 0 + 3 = 3 from by ring] at h; exact h
  step fm; finish

-- B≥9 reduction: inductive
theorem b9_reduce : ∀ k, ∀ a b, ⟨a+k, b+9*k, 3, 0⟩ [fm]⊢* ⟨a, b, 3, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 9 * (k + 1) = (b + 9 * k) + 9 from by ring]
  apply stepStar_trans (b9_step _ _)
  exact ih _ _

-- Base case B=8: 7 steps
theorem base_b8 : ∀ a, ⟨a, 8, 3, 0⟩ [fm]⊢* ⟨a, 0, 2, 0⟩ := by
  intro a
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Base case B=5: 17 steps
theorem base_b5 : ∀ a, ⟨a, 5, 3, 0⟩ [fm]⊢* ⟨a+2, 0, 2, 0⟩ := by
  intro a
  -- R1: (a,2,2,0) R2: (a+1,1,1,2) R2: (a+2,0,0,4)
  step fm; step fm; step fm
  -- R3×4
  apply stepStar_trans (d_to_b 4 (a+2) 0 0)
  -- R4: (a+1,4,3,0)
  step fm
  -- R1: (a+1,1,2,0) R2: (a+2,0,1,2)
  step fm; step fm
  -- R3: (a+2,1,1,1) R2: (a+3,0,0,3)
  step fm; step fm
  -- R3×3
  apply stepStar_trans (d_to_b 3 (a+3) 0 0)
  -- R4: (a+2,3,3,0) R1: (a+2,0,2,0)
  step fm; step fm
  ring_nf; finish

-- Base case B=2: compose with B=5
theorem base_b2 : ∀ a, ⟨a, 2, 3, 0⟩ [fm]⊢* ⟨a+4, 0, 2, 0⟩ := by
  intro a
  -- R2: (a+1,1,2,2) R2: (a+2,0,1,4)
  step fm; step fm
  -- R3: (a+2,1,1,3) R2: (a+3,0,0,5)
  step fm; step fm
  -- R3×5
  apply stepStar_trans (d_to_b 5 (a+3) 0 0)
  -- R4: (a+2,5,3,0)
  step fm
  -- Apply B=5 base case
  apply stepStar_trans (base_b5 (a+2))
  ring_nf; finish

-- Full chain: (0, 0, c+2, 0) ⊢⁺ (c, c+2, 3, 0)
theorem full_setup (c : ℕ) : ⟨0, 0, c+2, 0⟩ [fm]⊢⁺ ⟨c, c+2, 3, 0⟩ := by
  -- R5: (0, 0, c+1, 1)
  step fm
  -- Interleaved: (c+1, 0, 0, c+2)
  apply stepStar_trans
  · have h := interleaved c 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R3 transfer: (c+1, c+2, 0, 0)
  apply stepStar_trans
  · have h := d_to_b (c+2) (c+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R4: (c, c+2, 3, 0)
  step fm; finish

-- Drain phase: (c, c+2, 3, 0) ⊢* (result, 0, 2, 0)
-- Combines b9_reduce with appropriate base case

-- Transition for n ≡ 1 (mod 3): (3k+1, 0, 2, 0) ⊢⁺ (8k+5, 0, 2, 0)
theorem trans_mod1 (k : ℕ) : ⟨3*k+1, 0, 2, 0⟩ [fm]⊢⁺ ⟨8*k+5, 0, 2, 0⟩ := by
  -- R4 chain: (3k+1, 0, 2, 0) → (0, 0, 9k+5, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := a_to_c (3*k+1) 0 2
    simp only [Nat.zero_add] at h
    rw [show 2 + 3 * (3 * k + 1) = 9 * k + 5 from by ring] at h; exact h
  -- full_setup: (0, 0, 9k+5, 0) → (9k+3, 9k+5, 3, 0)
  apply stepPlus_stepStar_stepPlus
  · rw [show 9 * k + 5 = (9 * k + 3) + 2 from by ring]
    exact full_setup (9*k+3)
  -- B9 reduce k times: (9k+3, 9k+5, 3, 0) → (8k+3, 5, 3, 0)
  apply stepStar_trans
  · have h := b9_reduce k (8*k+3) 5
    rw [show 8 * k + 3 + k = 9 * k + 3 from by ring,
        show 5 + 9 * k = 9 * k + 5 from by ring] at h; exact h
  -- Base B=5: (8k+3, 5, 3, 0) → (8k+5, 0, 2, 0)
  have h := base_b5 (8*k+3)
  rw [show 8 * k + 3 + 2 = 8 * k + 5 from by ring] at h; exact h

-- Transition for n ≡ 2 (mod 3): (3k+2, 0, 2, 0) ⊢⁺ (8k+6, 0, 2, 0)
theorem trans_mod2 (k : ℕ) : ⟨3*k+2, 0, 2, 0⟩ [fm]⊢⁺ ⟨8*k+6, 0, 2, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := a_to_c (3*k+2) 0 2
    simp only [Nat.zero_add] at h
    rw [show 2 + 3 * (3 * k + 2) = 9 * k + 8 from by ring] at h; exact h
  apply stepPlus_stepStar_stepPlus
  · rw [show 9 * k + 8 = (9 * k + 6) + 2 from by ring]
    exact full_setup (9*k+6)
  apply stepStar_trans
  · have h := b9_reduce k (8*k+6) 8
    rw [show 8 * k + 6 + k = 9 * k + 6 from by ring,
        show 8 + 9 * k = 9 * k + 8 from by ring] at h; exact h
  exact base_b8 (8*k+6)

-- Transition for n ≡ 0 (mod 3): (3(k+1), 0, 2, 0) ⊢⁺ (8k+12, 0, 2, 0)
theorem trans_mod0 (k : ℕ) : ⟨3*k+3, 0, 2, 0⟩ [fm]⊢⁺ ⟨8*k+12, 0, 2, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := a_to_c (3*k+3) 0 2
    simp only [Nat.zero_add] at h
    rw [show 2 + 3 * (3 * k + 3) = 9 * k + 11 from by ring] at h; exact h
  apply stepPlus_stepStar_stepPlus
  · rw [show 9 * k + 11 = (9 * k + 9) + 2 from by ring]
    exact full_setup (9*k+9)
  apply stepStar_trans
  · have h := b9_reduce (k+1) (8*k+8) 2
    rw [show 8 * k + 8 + (k + 1) = 9 * k + 9 from by ring,
        show 2 + 9 * (k + 1) = 9 * k + 11 from by ring] at h; exact h
  have h := base_b2 (8*k+8)
  rw [show 8 * k + 8 + 4 = 8 * k + 12 from by ring] at h; exact h

-- Main transition
theorem main_trans : ∀ n, n ≥ 1 → ∃ n', n' ≥ 1 ∧ ⟨n, 0, 2, 0⟩ [fm]⊢⁺ ⟨n', 0, 2, 0⟩ := by
  intro n hn
  have hmod := Nat.div_add_mod n 3
  set q := n / 3
  set r := n % 3
  have hr : r < 3 := Nat.mod_lt n (by omega)
  interval_cases r
  · rcases q with _ | k
    · omega
    rw [show n = 3 * k + 3 from by omega]
    exact ⟨8*k+12, by omega, trans_mod0 k⟩
  · rw [show n = 3 * q + 1 from by omega]
    exact ⟨8*q+5, by omega, trans_mod1 q⟩
  · rw [show n = 3 * q + 2 from by omega]
    exact ⟨8*q+6, by omega, trans_mod2 q⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 2, 0⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨n, 0, 2, 0⟩ ∧ n ≥ 1)
  · intro c ⟨n, hq, hn⟩
    subst hq
    obtain ⟨n', hn', htrans⟩ := main_trans n hn
    exact ⟨⟨n', 0, 2, 0⟩, ⟨n', rfl, hn'⟩, htrans⟩
  · exact ⟨1, rfl, by omega⟩

end Sz22_2003_unofficial_21
