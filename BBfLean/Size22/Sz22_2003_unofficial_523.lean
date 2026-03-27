import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #523: [28/15, 3/847, 25/7, 11/5, 21/2]

Vector representation:
```
 2 -1 -1  1  0
 0  1  0 -1 -2
 0  0  2 -1  0
 0  0 -1  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_523

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R5/R2 drain: consume e in pairs, accumulating b
theorem r5r2_drain : ∀ k b a, ⟨a+k, b, 0, 0, 2*k+r⟩ [fm]⊢* ⟨a, b+2*k, 0, 0, r⟩ := by
  intro k; induction' k with k ih <;> intro b a
  · simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by omega,
      show 2 * (k + 1) + r = (2 * k + r) + 2 from by omega]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  rw [show b + 2 + 2 * k = b + 2 * (k + 1) from by omega]
  finish

-- R3 drain for e=0: convert d to c
theorem r3_drain_0 : ∀ j A c d, ⟨A, 0, c, d+j, 0⟩ [fm]⊢* ⟨A, 0, c+2*j, d, 0⟩ := by
  intro j; induction' j with j ih <;> intro A c d
  · simp only [Nat.mul_zero, Nat.add_zero]; exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by omega]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3 drain for e=1: convert d to c
theorem r3_drain_1 : ∀ j A c d, ⟨A, 0, c, d+j, 1⟩ [fm]⊢* ⟨A, 0, c+2*j, d, 1⟩ := by
  intro j; induction' j with j ih <;> intro A c d
  · simp only [Nat.mul_zero, Nat.add_zero]; exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by omega]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 drain: convert c to e
theorem r4_drain : ∀ j A c r, ⟨A, 0, c+j, 0, r⟩ [fm]⊢* ⟨A, 0, c, 0, r+j⟩ := by
  intro j; induction' j with j ih <;> intro A c r
  · simp only [Nat.add_zero]; exists 0
  rw [show c + (j + 1) = (c + j) + 1 from by omega]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R1/R1/R3 chain for e=0: (A, 2k+1, 2, D, 0) ->* (A+4k+2, 0, 1, D+k+1, 0)
theorem r1r3_chain_0 : ∀ k A D, ⟨A, 2*k+1, 2, D, 0⟩ [fm]⊢* ⟨A+4*k+2, 0, 1, D+k+1, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · step fm; ring_nf; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R1/R1/R3 chain for e=1: (A, 2k+1, 2, D, 1) ->* (A+4k+2, 0, 1, D+k+1, 1)
theorem r1r3_chain_1 : ∀ k A D, ⟨A, 2*k+1, 2, D, 1⟩ [fm]⊢* ⟨A+4*k+2, 0, 1, D+k+1, 1⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · step fm; ring_nf; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Even transition: (m+k+1, 0, 0, 0, 2*k) ->+ (m+4*k+2, 0, 0, 0, 2*k+3)
theorem even_trans : ⟨m+k+1, 0, 0, 0, 2*k⟩ [fm]⊢⁺ ⟨m+4*k+2, 0, 0, 0, 2*k+3⟩ := by
  rw [show m + k + 1 = (m + 1) + k from by omega,
      show 2 * k = 2 * k + 0 from by omega]
  apply stepStar_stepPlus_stepPlus (r5r2_drain (r := 0) k 0 (m+1))
  simp only [Nat.zero_add, Nat.add_zero]
  apply step_stepStar_stepPlus
  · show fm ⟨m+1, 2*k, 0, 0, 0⟩ = some ⟨m, 2*k+1, 0, 1, 0⟩; simp [fm]
  step fm
  apply stepStar_trans (r1r3_chain_0 k _ 0)
  simp only [Nat.zero_add]
  rw [show k + 1 = 0 + (k + 1) from by omega]
  apply stepStar_trans (r3_drain_0 (k+1) _ 1 0)
  rw [show 1 + 2 * (k + 1) = 2 * k + 3 from by omega,
      show 2 * k + 3 = 0 + (2 * k + 3) from by omega]
  apply stepStar_trans (r4_drain (2*k+3) _ 0 0)
  simp only [Nat.zero_add]; ring_nf; finish

-- Odd transition: (m+k+1, 0, 0, 0, 2*k+1) ->+ (m+4*k+2, 0, 0, 0, 2*k+4)
theorem odd_trans : ⟨m+k+1, 0, 0, 0, 2*k+1⟩ [fm]⊢⁺ ⟨m+4*k+2, 0, 0, 0, 2*k+4⟩ := by
  rw [show m + k + 1 = (m + 1) + k from by omega]
  apply stepStar_stepPlus_stepPlus (r5r2_drain (r := 1) k 0 (m+1))
  simp only [Nat.zero_add]
  apply step_stepStar_stepPlus
  · show fm ⟨m+1, 2*k, 0, 0, 1⟩ = some ⟨m, 2*k+1, 0, 1, 1⟩; simp [fm]
  step fm
  apply stepStar_trans (r1r3_chain_1 k _ 0)
  simp only [Nat.zero_add]
  rw [show k + 1 = 0 + (k + 1) from by omega]
  apply stepStar_trans (r3_drain_1 (k+1) _ 1 0)
  rw [show 1 + 2 * (k + 1) = 2 * k + 3 from by omega,
      show 2 * k + 3 = 0 + (2 * k + 3) from by omega]
  apply stepStar_trans (r4_drain (2*k+3) _ 0 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a n, q = ⟨a, 0, 0, 0, 3*n⟩ ∧ a ≥ 3*n/2 + 1)
  · intro c ⟨a, n, hq, ha⟩; subst hq
    rcases Nat.even_or_odd n with ⟨J, hJ⟩ | ⟨J, hJ⟩
    · -- n even: n = J + J = 2*J, e = 6*J, k = 3*J
      rw [show J + J = 2 * J from by omega] at hJ; subst hJ
      obtain ⟨m, rfl⟩ : ∃ m, a = m + 3*J + 1 := ⟨a - 3*J - 1, by omega⟩
      refine ⟨⟨m+12*J+2, 0, 0, 0, 3*(2*J+1)⟩,
        ⟨m+12*J+2, 2*J+1, rfl, by omega⟩, ?_⟩
      rw [show m + 3 * J + 1 = m + (3*J) + 1 from by omega,
          show 3 * (2 * J) = 2 * (3*J) from by omega,
          show m + 12 * J + 2 = m + 4 * (3*J) + 2 from by omega,
          show 3 * (2 * J + 1) = 2 * (3*J) + 3 from by omega]
      exact even_trans
    · -- n odd: n = 2*J + 1, e = 6*J+3, k = 3*J+1
      subst hJ
      obtain ⟨m, rfl⟩ : ∃ m, a = m + (3*J+1) + 1 := ⟨a - (3*J+1) - 1, by omega⟩
      refine ⟨⟨m+12*J+6, 0, 0, 0, 3*(2*J+2)⟩,
        ⟨m+12*J+6, 2*J+2, rfl, by omega⟩, ?_⟩
      rw [show 3 * (2 * J + 1) = 2 * (3*J+1) + 1 from by omega,
          show m + 12 * J + 6 = m + 4 * (3*J+1) + 2 from by omega,
          show 3 * (2 * J + 2) = 2 * (3*J+1) + 4 from by omega]
      exact odd_trans
  · exact ⟨2, 1, rfl, by omega⟩
