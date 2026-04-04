import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1875: [9/35, 484/5, 5/33, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  0
 2  0 -1  0  2
 0 -1  1  0 -1
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1875

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r3r2_chain : ∀ B, ⟨a, B, 0, 0, e + 1⟩ [fm]⊢* ⟨a + 2 * B, 0, 0, 0, e + 1 + B⟩ := by
  intro B; induction' B with B ih generalizing a e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

theorem d_drain_even : ∀ k a b, ⟨a + k, b, 0, 2 * k, 0⟩ [fm]⊢* ⟨a, b + 3 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm; step fm
    show ⟨a + k, b + 1 + 2, 0, 2 * k, 0⟩ [fm]⊢* ⟨a, b + 3 * (k + 1), 0, 0, 0⟩
    rw [show b + 1 + 2 = b + 3 from by ring,
        show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring]
    exact ih a (b + 3)

theorem d_drain_odd : ∀ k a b, ⟨a + k + 1, b, 0, 2 * k + 1, 0⟩ [fm]⊢* ⟨a, b + 3 * k + 2, 0, 0, 1⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · step fm; step fm; finish
  · rw [show a + (k + 1) + 1 = a + k + 1 + 1 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    step fm; step fm; step fm; step fm
    show ⟨a + k + 1, b + 1 + 2, 0, 2 * k + 1, 0⟩ [fm]⊢* ⟨a, b + 3 * (k + 1) + 2, 0, 0, 1⟩
    rw [show b + 1 + 2 = b + 3 from by ring,
        show b + 3 * (k + 1) + 2 = (b + 3) + 3 * k + 2 from by ring]
    exact ih a (b + 3)

theorem main_even : ⟨a + k + 1, 0, 0, 2 * k, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 2, 0, 0, 3 * k + 3, 0⟩ := by
  rw [show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (d_drain_even k (a + 1) 0)
  rw [show 0 + 3 * k = 3 * k from by ring,
      show a + 1 = (a + 0) + 1 from by ring]
  step fm; step fm
  show ⟨a + 0 + 2, 3 * k, 0, 0, 3⟩ [fm]⊢* ⟨a + 6 * k + 2, 0, 0, 3 * k + 3, 0⟩
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (3 * k) (a := a + 0 + 2) (e := 2))
  apply stepStar_trans (e_to_d (2 + 1 + 3 * k) (a := a + 0 + 2 + 2 * (3 * k)) (d := 0))
  ring_nf; finish

theorem main_odd : ⟨a + k + 1, 0, 0, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨a + 6 * k + 4, 0, 0, 3 * k + 3, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (d_drain_odd k a 0)
  rw [show 0 + 3 * k + 2 = 3 * k + 2 from by ring]
  step fm; step fm
  show ⟨a + 2, 3 * k + 1, 0, 0, 2⟩ [fm]⊢* ⟨a + 6 * k + 4, 0, 0, 3 * k + 3, 0⟩
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (3 * k + 1) (a := a + 2) (e := 1))
  apply stepStar_trans (e_to_d (1 + 1 + (3 * k + 1)) (a := a + 2 + 2 * (3 * k + 1)) (d := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ 2 * a ≥ d + 1)
  · intro c ⟨A, D, hq, hA⟩; subst hq
    rcases Nat.even_or_odd D with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨m, rfl⟩ : ∃ m, A = m + K + 1 := ⟨A - K - 1, by omega⟩
      exact ⟨⟨m + 6 * K + 2, 0, 0, 3 * K + 3, 0⟩,
        ⟨m + 6 * K + 2, 3 * K + 3, rfl, by omega⟩, main_even⟩
    · subst hK
      obtain ⟨m, rfl⟩ : ∃ m, A = m + K + 1 := ⟨A - K - 1, by omega⟩
      exact ⟨⟨m + 6 * K + 4, 0, 0, 3 * K + 3, 0⟩,
        ⟨m + 6 * K + 4, 3 * K + 3, rfl, by omega⟩, main_odd⟩
  · exact ⟨2, 3, rfl, by omega⟩
