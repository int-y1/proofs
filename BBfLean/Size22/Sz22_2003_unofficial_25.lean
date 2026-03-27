import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #25: [1/15, 18/77, 7/3, 5/7, 11979/2]

Vector representation:
```
 0 -1 -1  0  0
 1  2  0 -1 -1
 0 -1  0  1  0
 0  0  1 -1  0
-1  2  0  0  3
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_25

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+3⟩
  | _ => none

theorem b_drain : ∀ k : ℕ, ∀ a b d, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

theorem d_to_c : ∀ k : ℕ, ∀ a c d, ⟨a, 0, c, d+k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

theorem r3r2_chain : ∀ k : ℕ, ∀ a b, ⟨a, b+1, 0, 0, k⟩ [fm]⊢* ⟨a+k, b+k+1, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

theorem r5r1_even : ∀ k : ℕ, ∀ a e, ⟨a+k, 0, 2*k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+3*k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

theorem r5r1_odd : ∀ k : ℕ, ∀ a e, ⟨a+k+1, 0, 2*k+1, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 1, e+3*k+3⟩ := by
  intro k; induction' k with k h <;> intro a e
  · step fm; step fm; step fm; finish
  rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

theorem r5_chain (a e : ℕ) : ⟨a+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a+e+3, e+5, 0, 0, 0⟩ := by
  step fm
  have h := r3r2_chain (e + 3) a 1
  rw [show 1 + 1 = 2 from rfl, show 1 + (e + 3) + 1 = e + 5 from by ring] at h
  exact h

theorem r2_chain (a e : ℕ) : ⟨a, 0, 0, 1, e+1⟩ [fm]⊢⁺ ⟨a+e+1, e+2, 0, 0, 0⟩ := by
  step fm
  have h := r3r2_chain e (a + 1) 1
  rw [show 1 + 1 = 2 from rfl, show a + 1 + e = a + e + 1 from by ring,
      show 1 + e + 1 = e + 2 from by ring] at h
  exact h

theorem even_trans (a k : ℕ) : ⟨a+k+2, 2*(k+1), 0, 0, 0⟩ [fm]⊢⁺ ⟨a+3*k+6, 3*k+8, 0, 0, 0⟩ := by
  have h1 := b_drain (2*(k+1)) (a+k+2) 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  have h2 := d_to_c (2*(k+1)) (a+k+2) 0 0
  simp only [Nat.zero_add] at h2
  apply stepStar_stepPlus_stepPlus h2
  have h3 := r5r1_even (k+1) (a+1) 0
  rw [show (a + 1) + (k + 1) = a + k + 2 from by ring] at h3
  simp only [Nat.zero_add] at h3
  apply stepStar_stepPlus_stepPlus h3
  have h4 := r5_chain a (3 * (k + 1))
  rw [show a + 3 * (k + 1) + 3 = a + 3 * k + 6 from by ring,
      show 3 * (k + 1) + 5 = 3 * k + 8 from by ring] at h4
  exact h4

theorem odd_trans (a k : ℕ) : ⟨a+k+1, 2*k+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+3*k+3, 3*k+4, 0, 0, 0⟩ := by
  have h1 := b_drain (2*k+1) (a+k+1) 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  have h2 := d_to_c (2*k+1) (a+k+1) 0 0
  simp only [Nat.zero_add] at h2
  apply stepStar_stepPlus_stepPlus h2
  have h3 := r5r1_odd k a 0
  simp only [Nat.zero_add] at h3
  apply stepStar_stepPlus_stepPlus h3
  have h4 := r2_chain a (3 * k + 2)
  rw [show (3 : ℕ) * k + 2 + 1 = 3 * k + 3 from by ring,
      show a + (3 * k + 2) + 1 = a + 3 * k + 3 from by ring,
      show (3 : ℕ) * k + 2 + 2 = 3 * k + 4 from by ring] at h4
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 5, 0, 0, 0⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A B, q = ⟨A, B, 0, 0, 0⟩ ∧ B ≥ 5 ∧ 2 * A ≥ B + 1)
  · intro c ⟨A, B, hq, hB, hA⟩; subst hq
    rcases Nat.even_or_odd B with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- B even: B = K + K = 2*K
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, A = m + k + 2 := ⟨A - k - 2, by omega⟩
      exact ⟨⟨m+3*k+6, 3*k+8, 0, 0, 0⟩,
        ⟨m+3*k+6, 3*k+8, rfl, by omega, by omega⟩, even_trans m k⟩
    · -- B odd: B = 2*K + 1
      subst hK
      obtain ⟨m, rfl⟩ : ∃ m, A = m + K + 1 := ⟨A - K - 1, by omega⟩
      exact ⟨⟨m+3*K+3, 3*K+4, 0, 0, 0⟩,
        ⟨m+3*K+3, 3*K+4, rfl, by omega, by omega⟩, odd_trans m K⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩
