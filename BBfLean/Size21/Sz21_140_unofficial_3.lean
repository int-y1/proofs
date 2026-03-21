import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #3: [1/15, 9/77, 98/3, 5/7, 99/2]

Vector representation:
```
 0 -1 -1  0  0
 0  2  0 -1 -1
 1 -1  0  2  0
 0  0  1 -1  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_3

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R4 chain: d → c
theorem d_to_c : ∀ k, ∀ a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (h a (c+1))
  ring_nf; finish

-- R5/R1/R1 single round
theorem r5r1r1_step : ⟨a+1, 0, c+2, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+1⟩ := by
  step fm; step fm; step fm; finish

-- R5/R1/R1 chain for even c
theorem r5r1r1_even : ∀ k, ∀ a e, ⟨a+k, 0, 2*k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show a + (k + 1) = a + k + 1 from by ring,
      show 2 * (k + 1) = 2 * k + 2 from by ring]
  apply stepStar_trans (@r5r1r1_step (a+k) (2*k) e)
  apply stepStar_trans (h a (e+1))
  ring_nf; finish

-- R5/R1/R1 chain for odd c
theorem r5r1r1_odd : ∀ k, ∀ a e, ⟨a+k, 0, 2*k+1, 0, e⟩ [fm]⊢* ⟨a, 0, 1, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show a + (k + 1) = a + k + 1 from by ring,
      show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
  apply stepStar_trans (@r5r1r1_step (a+k) (2*k+1) e)
  apply stepStar_trans (h a (e+1))
  ring_nf; finish

-- Pure R3 chain
theorem pure_r3_chain : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a+k, 0, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  step fm
  apply stepStar_trans (h (a+1) (d+2))
  ring_nf; finish

-- Combined R3/R2/R2 + R3 chain
theorem r3r2r2_r3 : ∀ K, ∀ a b, ⟨a, b+1, 0, 0, K⟩ [fm]⊢* ⟨a+b+1+2*K, 0, 0, 2*b+2+3*K, 0⟩ := by
  intro K; induction' K using Nat.strongRecOn with K ih; intro a b
  rcases K with _ | _ | K
  · have h := @pure_r3_chain (b+1) a 0
    refine stepStar_trans h ?_; ring_nf; finish
  · step fm; step fm
    have h := @pure_r3_chain (b+2) (a+1) 1
    refine stepStar_trans h ?_; ring_nf; finish
  · step fm
    rw [show K + 2 = (K + 1) + 1 from by ring]
    step fm; step fm
    rw [show b + 4 = (b + 3) + 1 from by ring]
    have h := ih K (by omega) (a+1) (b+3)
    refine stepStar_trans h ?_; ring_nf; finish

-- Phase C base
theorem phase_c_base : ⟨a+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+4, 0, 0, 7, 0⟩ := by
  execute fm 6

-- Phase C successor
theorem phase_c_succ : ⟨a+1, 0, 0, 0, k+1⟩ [fm]⊢⁺ ⟨a+2*k+6, 0, 0, 3*k+10, 0⟩ := by
  step fm; step fm
  rw [show k + 2 = (k + 1) + 1 from by ring]
  step fm; step fm
  rw [show (5 : ℕ) = 4 + 1 from by ring]
  have h := @r3r2r2_r3 k (a+1) 4
  refine stepStar_trans h ?_; ring_nf; finish

-- Even transition
theorem even_trans : ∀ k, ⟨a+1+k, 0, 0, 2*k, 0⟩ [fm]⊢⁺ ⟨a+2*k+4, 0, 0, 3*k+7, 0⟩ := by
  intro k; rcases k with _ | k
  · simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    exact phase_c_base
  · apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1+(k+1), 0, 2*(k+1), 0, 0⟩)
    · have h := d_to_c (2*(k+1)) (a+1+(k+1)) 0
      simp only [Nat.zero_add] at h; exact h
    apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 0, k+1⟩)
    · have h := r5r1r1_even (k+1) (a+1) 0
      simp only [Nat.zero_add] at h; exact h
    have h := @phase_c_succ a k
    refine stepPlus_stepStar_stepPlus h ?_; ring_nf; finish

-- Odd tail base
theorem odd_tail_base : ⟨a+1, 0, 1, 0, 0⟩ [fm]⊢⁺ ⟨a+3, 0, 0, 5, 0⟩ := by
  execute fm 6

-- Odd tail successor
theorem odd_tail_succ : ⟨a+1, 0, 1, 0, k+1⟩ [fm]⊢⁺ ⟨a+2*k+5, 0, 0, 3*k+8, 0⟩ := by
  step fm; step fm; step fm
  rw [show k + 2 = (k + 1) + 1 from by ring]
  step fm; step fm
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  have h := @r3r2r2_r3 k (a+1) 3
  refine stepStar_trans h ?_; ring_nf; finish

-- Odd transition
theorem odd_trans : ∀ k, ⟨a+1+k, 0, 0, 2*k+1, 0⟩ [fm]⊢⁺ ⟨a+2*k+3, 0, 0, 3*k+5, 0⟩ := by
  intro k
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1+k, 0, 2*k+1, 0, 0⟩)
  · have h := d_to_c (2*k+1) (a+1+k) 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 1, 0, k⟩)
  · have h := r5r1r1_odd k (a+1) 0
    simp only [Nat.zero_add] at h; exact h
  rcases k with _ | k
  · simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    exact odd_tail_base
  · have h := @odd_tail_succ a k
    refine stepPlus_stepStar_stepPlus h ?_; ring_nf; finish

-- Main theorem
theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a+1, 0, 0, d, 0⟩ ∧ d ≤ 2*a+1)
  · intro q ⟨a, d, hq, hd⟩; subst hq
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      have hka : k ≤ a := by omega
      refine ⟨⟨a+k+4, 0, 0, 3*k+7, 0⟩, ⟨a+k+3, 3*k+7, by ring_nf, by omega⟩, ?_⟩
      rw [show k + k = 2 * k from by ring]
      have h := @even_trans (a-k) k
      rw [show a - k + 1 + k = a + 1 from by omega,
          show a - k + 2 * k + 4 = a + k + 4 from by omega] at h
      exact h
    · subst hk
      have hka : k ≤ a := by omega
      refine ⟨⟨a+k+3, 0, 0, 3*k+5, 0⟩, ⟨a+k+2, 3*k+5, by ring_nf, by omega⟩, ?_⟩
      have h := @odd_trans (a-k) k
      rw [show a - k + 1 + k = a + 1 from by omega,
          show a - k + 2 * k + 3 = a + k + 3 from by omega] at h
      exact h
  · exact ⟨0, 0, rfl, by omega⟩
