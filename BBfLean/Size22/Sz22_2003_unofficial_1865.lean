import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1865: [9/35, 242/5, 5/33, 7/121, 15/2]

Vector representation:
```
 0  2 -1 -1  0
 1  0 -1  0  2
 0 -1  1  0 -1
 0  0  0  1 -2
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1865

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, 2 * k + r⟩ [fm]⊢* ⟨a, 0, 0, d + k, r⟩ := by
  intro k; induction' k with k ih generalizing d
  · simp; exists 0
  · rw [show 2 * (k + 1) + r = (2 * k + r) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem drain_d : ∀ d, ⟨a + d, b, 0, d, 0⟩ [fm]⊢* ⟨a, b + 3 * d, 0, 0, 0⟩ := by
  intro d; induction' d with d ih generalizing a b
  · simp; exists 0
  · rw [show a + (d + 1) = (a + d) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a) (b := b + 3))
    ring_nf; finish

theorem r3r2_chain : ∀ B, ⟨a, B, 0, 0, e + 1⟩ [fm]⊢* ⟨a + B, 0, 0, 0, e + 1 + B⟩ := by
  intro B; induction' B with B ih generalizing a e
  · simp; exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem odd_drain : ∀ k, ⟨a + k + 1, 0, 0, k + 1, 1⟩ [fm]⊢* ⟨a, 3 * k + 2, 1, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a
  · step fm; step fm; step fm; finish
  · rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show (k + 1) + 1 = k + 2 from by ring]
    step fm
    step fm
    step fm
    step fm
    rw [show a + k + 1 = a + 1 + k from by ring]
    apply stepStar_trans (drain_d k (a := a + 1) (b := 4))
    rw [show 4 + 3 * k = 3 * k + 4 from by ring]
    step fm
    rw [show 3 * (k + 1) + 2 = 3 * k + 5 from by ring]
    finish

theorem even_trans : ⟨a + k + 2, 0, 0, 0, 2 * (k + 1)⟩ [fm]⊢⁺ ⟨a + 3 * k + 5, 0, 0, 0, 3 * k + 6⟩ := by
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans (e_to_d (k + 1) (a := a + k + 2) (d := 0) (r := 0))
    rw [show 0 + (k + 1) = k + 1 from by omega,
        show a + k + 2 = (a + 1) + (k + 1) from by ring]
    exact drain_d (k + 1) (a := a + 1) (b := 0)
  · rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
    show ⟨a + 1, 3 * k + 3, 0, 0, 0⟩ [fm]⊢⁺ _
    step fm
    step fm
    rw [show 3 * k + 3 + 1 = 3 * k + 4 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (r3r2_chain (3 * k + 4) (a := a + 1) (e := 1))
    ring_nf; finish

theorem odd_trans : ⟨a + k + 1, 0, 0, 0, 2 * (k + 1) + 1⟩ [fm]⊢⁺ ⟨a + 3 * k + 3, 0, 0, 0, 3 * k + 4⟩ := by
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans (e_to_d (k + 1) (a := a + k + 1) (d := 0) (r := 1))
    rw [show 0 + (k + 1) = k + 1 from by omega]
    exact odd_drain k (a := a)
  · show ⟨a, 3 * k + 2, 1, 0, 0⟩ [fm]⊢⁺ _
    step fm
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (r3r2_chain (3 * k + 2) (a := a + 1) (e := 1))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 3 ∧ 2 * a ≥ e + 1)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      exact ⟨⟨m + 3 * k + 5, 0, 0, 0, 3 * k + 6⟩,
        ⟨m + 3 * k + 5, 3 * k + 6, rfl, by omega, by omega⟩, even_trans⟩
    · subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨⟨m + 3 * k + 3, 0, 0, 0, 3 * k + 4⟩,
        ⟨m + 3 * k + 3, 3 * k + 4, rfl, by omega, by omega⟩, odd_trans⟩
  · exact ⟨2, 3, rfl, by omega, by omega⟩
