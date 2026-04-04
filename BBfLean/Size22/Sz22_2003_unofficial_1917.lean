import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1917: [9/385, 7/15, 50/7, 11/2, 49/11]

Vector representation:
```
 0  2 -1 -1 -1
 0 -1 -1  1  0
 1  0  2 -1  0
-1  0  0  0  1
 0  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1917

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · exact stepStar_trans (step_stepStar (by simp [fm] : fm ⟨k + 1, 0, c, 0, e⟩ = some ⟨k, 0, c, 0, e + 1⟩))
      (by apply stepStar_trans (ih c (e + 1)); ring_nf; finish)

theorem r3_chain : ∀ k, ∀ a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · exact stepStar_trans (step_stepStar (by simp [fm] : fm ⟨a, 0, c, k + 1, 0⟩ = some ⟨a + 1, 0, c + 2, k, 0⟩))
      (by apply stepStar_trans (ih (a + 1) (c + 2)); ring_nf; finish)

theorem r2r1_pair : ⟨0, b + 1, c + 2, 0, e + 1⟩ [fm]⊢* ⟨0, b + 2, c, 0, e⟩ := by
  step fm; step fm; finish

theorem r2r1_loop : ∀ k, ∀ b c e,
    ⟨0, b + 1, c + 2 * k + 2, 0, e + k + 1⟩ [fm]⊢* ⟨0, b + k + 1, c + 2, 0, e + 1⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + 2 * (k + 1) + 2 = (c + 2 * k + 2) + 2 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    apply stepStar_trans (r2r1_pair (b := b) (c := c + 2 * k + 2) (e := e + k + 1))
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) c e); ring_nf; finish

theorem r2r2r3_drain : ∀ k, ∀ a b,
    ⟨a + 2, b + 2 * k + 3, 2, 0, 0⟩ [fm]⊢* ⟨a + k + 3, b + 1, 2, k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    step fm; ring_nf; finish
  · rw [show b + 2 * (k + 1) + 3 = (b + 2) + 2 * k + 3 from by ring]
    apply stepStar_trans (ih a (b + 2))
    rw [show b + 2 + 1 = b + 3 from by ring]
    step fm; step fm
    rw [show a + k + 3 = (a + k + 2) + 1 from by ring]
    step fm; ring_nf; finish

theorem micro_cycle : ⟨2, b, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨2, b + 2, 0, 0, e⟩ := by
  execute fm 9

theorem micro_chain : ∀ k, ∀ b, ⟨2, b, 0, 0, k⟩ [fm]⊢* ⟨2, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · apply stepStar_trans (stepPlus_stepStar (micro_cycle (b := b) (e := k)))
    apply stepStar_trans (ih (b + 2)); ring_nf; finish

theorem even_first_half : ∀ n,
    ⟨2, 2 * n + 12, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 15, 0, 2 * n + 15, 0, 0⟩ := by
  intro n
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨2, 2 * n + 13, 2, 0, 0⟩ [fm]⊢* ⟨2 * n + 15, 0, 2 * n + 15, 0, 0⟩
  rw [show 2 * n + 13 = 0 + 2 * (n + 5) + 3 from by ring]
  apply stepStar_trans (r2r2r3_drain (n + 5) 0 0)
  rw [show 0 + (n + 5) + 3 = n + 8 from by ring,
      show 0 + 1 = 1 from by ring,
      show (n : ℕ) + 5 + 1 = n + 6 from by ring]
  step fm
  show ⟨n + 8, 0, 1, n + 7, 0⟩ [fm]⊢* ⟨2 * n + 15, 0, 2 * n + 15, 0, 0⟩
  apply stepStar_trans (r3_chain (n + 7) (n + 8) 1)
  ring_nf; finish

theorem odd_first_half : ∀ n,
    ⟨2, 2 * n + 13, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 16, 0, 2 * n + 16, 0, 0⟩ := by
  intro n
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨2, 2 * n + 14, 2, 0, 0⟩ [fm]⊢* ⟨2 * n + 16, 0, 2 * n + 16, 0, 0⟩
  rw [show 2 * n + 14 = 1 + 2 * (n + 5) + 3 from by ring]
  apply stepStar_trans (r2r2r3_drain (n + 5) 0 1)
  rw [show 0 + (n + 5) + 3 = n + 8 from by ring,
      show 1 + 1 = 2 from by ring,
      show (n : ℕ) + 5 + 1 = n + 6 from by ring]
  step fm; step fm
  show ⟨n + 8, 0, 0, n + 8, 0⟩ [fm]⊢* ⟨2 * n + 16, 0, 2 * n + 16, 0, 0⟩
  apply stepStar_trans (r3_chain (n + 8) (n + 8) 0)
  ring_nf; finish

theorem second_half_even : ∀ n,
    ⟨0, 0, 2 * n + 16, 0, 2 * n + 16⟩ [fm]⊢* ⟨2, 3 * n + 19, 0, 0, 0⟩ := by
  intro n
  step fm; step fm; step fm
  show ⟨0, 4, 2 * n + 14, 0, 2 * n + 13⟩ [fm]⊢* ⟨2, 3 * n + 19, 0, 0, 0⟩
  rw [show 2 * n + 14 = 2 + 2 * (n + 5) + 2 from by ring,
      show 2 * n + 13 = (n + 7) + (n + 5) + 1 from by ring]
  apply stepStar_trans (r2r1_loop (n + 5) 3 2 (n + 7))
  rw [show 3 + (n + 5) + 1 = n + 9 from by ring,
      show (2 : ℕ) + 2 = 4 from by ring,
      show n + 7 + 1 = n + 8 from by ring]
  step fm; step fm; step fm; step fm
  show ⟨0, n + 11, 0, 0, n + 6⟩ [fm]⊢* ⟨2, 3 * n + 19, 0, 0, 0⟩
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨2, n + 13, 0, 0, n + 3⟩ [fm]⊢* ⟨2, 3 * n + 19, 0, 0, 0⟩
  apply stepStar_trans (micro_chain (n + 3) (n + 13))
  ring_nf; finish

theorem second_half_odd : ∀ n,
    ⟨0, 0, 2 * n + 15, 0, 2 * n + 15⟩ [fm]⊢* ⟨2, 3 * n + 18, 0, 0, 0⟩ := by
  intro n
  step fm; step fm; step fm
  show ⟨0, 4, 2 * n + 13, 0, 2 * n + 12⟩ [fm]⊢* ⟨2, 3 * n + 18, 0, 0, 0⟩
  rw [show 2 * n + 13 = 1 + 2 * (n + 5) + 2 from by ring,
      show 2 * n + 12 = (n + 6) + (n + 5) + 1 from by ring]
  apply stepStar_trans (r2r1_loop (n + 5) 3 1 (n + 6))
  rw [show 3 + (n + 5) + 1 = n + 9 from by ring,
      show (1 : ℕ) + 2 = 3 from by ring,
      show n + 6 + 1 = n + 7 from by ring]
  step fm; step fm
  show ⟨0, n + 10, 1, 0, n + 6⟩ [fm]⊢* ⟨2, 3 * n + 18, 0, 0, 0⟩
  step fm; step fm; step fm; step fm
  show ⟨1, n + 10, 0, 0, n + 5⟩ [fm]⊢* ⟨2, 3 * n + 18, 0, 0, 0⟩
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨2, n + 12, 0, 0, n + 3⟩ [fm]⊢* ⟨2, 3 * n + 18, 0, 0, 0⟩
  apply stepStar_trans (micro_chain (n + 3) (n + 12))
  ring_nf; finish

theorem even_trans : ∀ n, ⟨2, 2 * n + 12, 0, 0, 0⟩ [fm]⊢⁺ ⟨2, 3 * n + 18, 0, 0, 0⟩ := by
  intro n
  apply stepPlus_stepStar_stepPlus (even_first_half n)
  apply stepStar_trans (r4_drain (2 * n + 15) (2 * n + 15) 0)
  rw [show 0 + (2 * n + 15) = 2 * n + 15 from by ring]
  exact second_half_odd n

theorem odd_trans : ∀ n, ⟨2, 2 * n + 13, 0, 0, 0⟩ [fm]⊢⁺ ⟨2, 3 * n + 19, 0, 0, 0⟩ := by
  intro n
  apply stepPlus_stepStar_stepPlus (odd_first_half n)
  apply stepStar_trans (r4_drain (2 * n + 16) (2 * n + 16) 0)
  rw [show 0 + (2 * n + 16) = 2 * n + 16 from by ring]
  exact second_half_even n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 12, 0, 0, 0⟩) (by execute fm 228)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ b, q = ⟨2, b + 12, 0, 0, 0⟩)
  · intro c ⟨b, hq⟩; subst hq
    rcases Nat.even_or_odd b with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      exact ⟨⟨2, 3 * K + 18, 0, 0, 0⟩,
        ⟨3 * K + 6, by ring_nf⟩, even_trans K⟩
    · subst hK
      exact ⟨⟨2, 3 * K + 19, 0, 0, 0⟩,
        ⟨3 * K + 7, by ring_nf⟩, odd_trans K⟩
  · exact ⟨0, rfl⟩
