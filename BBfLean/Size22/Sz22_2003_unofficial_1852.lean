import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1852: [9/35, 121/5, 10/33, 7/121, 15/2]

Vector representation:
```
 0  2 -1 -1  0
 0  0 -1  0  2
 1 -1  1  0 -1
 0  0  0  1 -2
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1852

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r4_drain : ∀ k, ⟨a, 0, 0, d, e + 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem drain_d_e0 : ∀ k, ⟨a + k, b, 0, k, 0⟩ [fm]⊢* ⟨a, b + 3 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a) (b := b + 3))
    ring_nf; finish

theorem r3r2_loop : ∀ k, ⟨a, b + k, 0, 0, e + 1⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem phase3a : ⟨a + 1, b, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + b + 1, 0, 0, 0, b + 3⟩ := by
  step fm; step fm; step fm; step fm
  rw [show (b : ℕ) = 0 + b from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_loop b (a := a + 1) (b := 0) (e := 2))
  ring_nf; finish

theorem phase3b : ⟨a, b + 1, 0, 0, 1⟩ [fm]⊢⁺ ⟨a + b + 1, 0, 0, 0, b + 2⟩ := by
  step fm; step fm
  rw [show (b : ℕ) = 0 + b from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_loop b (a := a + 1) (b := 0) (e := 1))
  ring_nf; finish

theorem drain_d1_e1 : ⟨a + 1, 0, 0, 1, 1⟩ [fm]⊢⁺ ⟨a, 3, 0, 0, 1⟩ := by
  step fm; step fm; finish

theorem drain_dk_e1 : ∀ k, ⟨a + k + 3, 0, 0, k + 2, 1⟩ [fm]⊢⁺ ⟨a + 3, 3 * k + 4, 0, 0, 0⟩ := by
  intro k
  rw [show a + k + 3 = (a + k + 2) + 1 from by ring]
  step fm; step fm; step fm; step fm
  show ⟨a + k + 3, 4, 0, k, 0⟩ [fm]⊢* ⟨a + 3, 3 * k + 4, 0, 0, 0⟩
  rw [show a + k + 3 = (a + 3) + k from by ring]
  apply stepStar_trans (drain_d_e0 k (a := a + 3) (b := 4))
  ring_nf; finish

theorem even_trans : ∀ k, ⟨a + k + 3, 0, 0, 0, 2 * k + 4⟩ [fm]⊢⁺
    ⟨a + 3 * k + 7, 0, 0, 0, 3 * k + 9⟩ := by
  intro k
  rw [show 2 * k + 4 = 0 + 2 * (k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (k + 2) (a := a + k + 3) (d := 0) (e := 0))
  rw [show 0 + (k + 2) = k + 2 from by ring,
      show a + k + 3 = (a + 1) + (k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_d_e0 (k + 2) (a := a + 1) (b := 0))
  rw [show 0 + 3 * (k + 2) = 3 * k + 6 from by ring]
  show ⟨a + 1, 3 * k + 6, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 3 * k + 7, 0, 0, 0, 3 * k + 9⟩
  apply stepPlus_stepStar_stepPlus (phase3a (a := a) (b := 3 * k + 6))
  ring_nf; finish

theorem odd_trans_d1 : ⟨a + 1, 0, 0, 0, 3⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 0, 4⟩ := by
  step fm
  apply stepStar_trans (stepPlus_stepStar (drain_d1_e1 (a := a)))
  rw [show (3 : ℕ) = 0 + 3 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2_loop 3 (a := a) (b := 0) (e := 0))
  ring_nf; finish

theorem odd_trans : ∀ k, ⟨a + k + 3, 0, 0, 0, 2 * k + 5⟩ [fm]⊢⁺
    ⟨a + 3 * k + 7, 0, 0, 0, 3 * k + 7⟩ := by
  intro k
  rw [show 2 * k + 5 = 1 + 2 * (k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (k + 2) (a := a + k + 3) (d := 0) (e := 1))
  rw [show 0 + (k + 2) = k + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (drain_dk_e1 k (a := a))
  show ⟨a + 3, 3 * k + 4, 0, 0, 0⟩ [fm]⊢* ⟨a + 3 * k + 7, 0, 0, 0, 3 * k + 7⟩
  apply stepStar_trans (stepPlus_stepStar (phase3a (a := a + 2) (b := 3 * k + 4)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 4⟩) (by execute fm 13)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 4 ∧ 2 * a ≥ e + 2)
  · intro c ⟨A, E, hq, hE, hA⟩; subst hq
    rcases Nat.even_or_odd E with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, A = m + k + 3 := ⟨A - k - 3, by omega⟩
      exact ⟨⟨m + 3 * k + 7, 0, 0, 0, 3 * k + 9⟩,
        ⟨m + 3 * k + 7, 3 * k + 9, rfl, by omega, by omega⟩, even_trans k (a := m)⟩
    · subst hK
      rcases K with _ | _ | K'
      · omega
      · obtain ⟨m, rfl⟩ : ∃ m, A = m + 1 := ⟨A - 1, by omega⟩
        exact ⟨⟨m + 3, 0, 0, 0, 4⟩,
          ⟨m + 3, 4, rfl, by omega, by omega⟩, odd_trans_d1 (a := m)⟩
      · obtain ⟨m, rfl⟩ : ∃ m, A = m + K' + 3 := ⟨A - K' - 3, by omega⟩
        exact ⟨⟨m + 3 * K' + 7, 0, 0, 0, 3 * K' + 7⟩,
          ⟨m + 3 * K' + 7, 3 * K' + 7, rfl, by omega, by omega⟩, odd_trans K' (a := m)⟩
  · exact ⟨3, 4, rfl, by omega, by omega⟩
