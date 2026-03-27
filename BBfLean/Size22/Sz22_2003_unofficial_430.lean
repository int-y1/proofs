import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #430: [27/35, 1/33, 25/3, 22/25, 21/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  0  0 -1
 0 -1  2  0  0
 1  0 -2  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

The machine has Collatz-like dynamics: from the canonical state (a, 0, 0, d, 0),
the transition to the next canonical state depends on d parity:
- d even: a' = a+2, d' = (5d-2)/2
- d odd:  a' = a-1, d' = (5d+7)/2

The key invariant is that a (equivalently delta = A-E in the pre-drain form)
changes by +2 for even d and -1 for odd d, starting from delta=3. The odd chain
(sequence of consecutive odd d values) has Collatz-like termination behavior,
making a fully formal proof challenging.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_430

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r1r1r3_chain : ∀ k, ∀ A B D,
    ⟨A, B, 2, D + 2 * k, 0⟩ [fm]⊢* ⟨A, B + 5 * k, 2, D, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B D
  · exists 0
  rw [show D + 2 * (k + 1) = (D + 2 * k) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih A (B + 6) D); ring_nf; finish

theorem r3_drain : ∀ B, ∀ A C,
    ⟨A, B, C, 0, 0⟩ [fm]⊢* ⟨A, 0, C + 2 * B, 0, 0⟩ := by
  intro B; induction' B with B ih <;> intro A C
  · exists 0
  rw [show C + 2 * (B + 1) = (C + 2) + 2 * B from by ring]
  step fm; apply stepStar_trans (ih A (C + 2)); ring_nf; finish

theorem r4_chain : ∀ k, ∀ A C E,
    ⟨A, 0, C + 2 * k, 0, E⟩ [fm]⊢* ⟨A + k, 0, C, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A C E
  · exists 0
  rw [show C + 2 * (k + 1) = (C + 2 * k) + 2 from by ring]
  step fm; apply stepStar_trans (ih (A + 1) C E); ring_nf; finish

theorem r5r2_drain : ∀ k, ∀ A D,
    ⟨A + 1 + k, 0, 0, D, k + 1⟩ [fm]⊢* ⟨A, 0, 0, D + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro A D
  · step fm; step fm; finish
  rw [show A + 1 + (k + 1) = (A + 1 + k) + 1 from by ring]
  step fm; step fm; apply stepStar_trans (ih A (D + 1)); ring_nf; finish

theorem buildup : ∀ D, ∀ A,
    ⟨A, 0, 2, D, 0⟩ [fm]⊢* ⟨A, 0, 5 * D + 2, 0, 0⟩ := by
  intro D A
  rcases Nat.even_or_odd D with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    apply stepStar_trans (r1r1r3_chain k A 0 0)
    simp only [Nat.zero_add]
    apply stepStar_trans (r3_drain (5 * k) A 2); ring_nf; finish
  · subst hk
    apply stepStar_trans (r1r1r3_chain k A 0 1)
    simp only [Nat.zero_add]; step fm
    apply stepStar_trans (r3_drain (5 * k + 3) A 1); ring_nf; finish

theorem even_trans (a d : ℕ) :
    ⟨a + 1, 0, 0, 2 * d + 2, 0⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 5 * d + 4, 0⟩ := by
  apply step_stepStar_stepPlus; step fm
  apply stepStar_trans (buildup (2 * d + 3) a)
  rw [show 5 * (2 * d + 3) + 2 = 2 * (5 * d + 8) + 1 from by ring]
  apply stepStar_trans
  · have h := r4_chain (5 * d + 8) a 1 0
    rw [show 1 + 2 * (5 * d + 8) = 2 * (5 * d + 8) + 1 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  step fm; step fm; step fm; step fm; step fm; step fm
  rw [show a + (5 * d + 8) = a + 3 + 1 + (5 * d + 3) from by omega,
      show 5 * d + 4 = (5 * d + 3) + 1 from by omega]
  exact r5r2_drain (5 * d + 3) (a + 3) 0

theorem odd_trans (a d : ℕ) :
    ⟨a + 1, 0, 0, 2 * d + 1, 0⟩ [fm]⊢⁺ ⟨a, 0, 0, 5 * d + 6, 0⟩ := by
  apply step_stepStar_stepPlus; step fm
  apply stepStar_trans (buildup (2 * d + 2) a)
  rw [show 5 * (2 * d + 2) + 2 = 2 * (5 * d + 6) from by ring]
  apply stepStar_trans
  · have h := r4_chain (5 * d + 6) a 0 0
    simp only [Nat.zero_add] at h; exact h
  rw [show a + (5 * d + 6) = a + 1 + (5 * d + 5) from by omega,
      show 5 * d + 6 = (5 * d + 5) + 1 from by omega]
  exact r5r2_drain (5 * d + 5) a 0

theorem nonhalt : ¬halts fm c₀ := by
  sorry

end Sz22_2003_unofficial_430
