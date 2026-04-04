import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1976: [99/35, 25/6, 2/5, 7/11, 175/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  2  0  0
 1  0 -1  0  0
 0  0  0  1 -1
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1976

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

theorem round_chain : ∀ k, ⟨a + k, B, 2, D + 2 * k, E⟩ [fm]⊢* ⟨a, B + 3 * k, 2, D, E + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a B D E
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show D + 2 * (k + 1) = (D + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (D := D + 2))
    step fm; step fm; step fm
    ring_nf; finish

theorem R4_chain : ∀ k, ⟨a, 0, 0, D, k⟩ [fm]⊢* ⟨a, 0, 0, D + k, 0⟩ := by
  intro k; induction' k with k ih generalizing D
  · exists 0
  · rw [show D + (k + 1) = (D + 1) + k from by ring]
    step fm
    apply stepStar_trans (ih (D := D + 1))
    ring_nf; finish

theorem R3_chain : ∀ k, ⟨a, 0, k, 0, E⟩ [fm]⊢* ⟨a + k, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

theorem drain_bc : ∀ b, ∀ a c e, ⟨a, b, c + 1, 0, e⟩ [fm]⊢* ⟨a + b + c + 1, 0, 0, 0, e⟩ := by
  intro b; induction' b with b ih <;> intro a c e
  · apply stepStar_trans (R3_chain (c + 1) (a := a) (E := e))
    ring_nf; finish
  · rcases a with _ | a'
    · step fm; step fm
      apply stepStar_trans (ih 0 (c + 1) e)
      ring_nf; finish
    · step fm
      apply stepStar_trans (ih a' (c + 2) e)
      ring_nf; finish

theorem main_trans_even : ∀ m, ⟨a + 2 * m + 2, 0, 0, 2 * m + 1, 0⟩ [fm]⊢⁺ ⟨a + 4 * m + 5, 0, 0, 2 * m + 2, 0⟩ := by
  intro m
  step fm
  show ⟨a + 2 * m + 1, 0, 2, 2 * m + 1 + 1, 0⟩ [fm]⊢* ⟨a + 4 * m + 5, 0, 0, 2 * m + 2, 0⟩
  rw [show a + 2 * m + 1 = a + m + (m + 1) from by ring,
      show 2 * m + 1 + 1 = 0 + 2 * (m + 1) from by ring]
  apply stepStar_trans (round_chain (m + 1) (a := a + m) (B := 0) (D := 0) (E := 0))
  rw [show 0 + 3 * (m + 1) = 3 * m + 3 from by ring,
      show 0 + 2 * (m + 1) = 2 * m + 2 from by ring]
  apply stepStar_trans (drain_bc (3 * m + 3) (a + m) 1 (2 * m + 2))
  rw [show a + m + (3 * m + 3) + 1 + 1 = a + 4 * m + 5 from by ring]
  apply stepStar_trans (R4_chain (2 * m + 2) (a := a + 4 * m + 5) (D := 0))
  ring_nf; finish

theorem main_trans_odd : ∀ m, ⟨a + 2 * m + 3, 0, 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨a + 4 * m + 7, 0, 0, 2 * m + 3, 0⟩ := by
  intro m
  step fm
  show ⟨a + 2 * m + 2, 0, 2, 2 * m + 2 + 1, 0⟩ [fm]⊢* ⟨a + 4 * m + 7, 0, 0, 2 * m + 3, 0⟩
  rw [show a + 2 * m + 2 = a + m + 1 + (m + 1) from by ring,
      show 2 * m + 2 + 1 = 1 + 2 * (m + 1) from by ring]
  apply stepStar_trans (round_chain (m + 1) (a := a + m + 1) (B := 0) (D := 1) (E := 0))
  rw [show 0 + 3 * (m + 1) = 3 * m + 3 from by ring,
      show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
      show 1 + 2 * (m + 1) = 2 * m + 3 from by ring]
  step fm; step fm
  show ⟨a + m, 3 * m + 4, 3, 0, 2 * m + 3⟩ [fm]⊢* ⟨a + 4 * m + 7, 0, 0, 2 * m + 3, 0⟩
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (drain_bc (3 * m + 4) (a + m) 2 (2 * m + 3))
  rw [show a + m + (3 * m + 4) + 2 + 1 = a + 4 * m + 7 from by ring]
  apply stepStar_trans (R4_chain (2 * m + 3) (a := a + 4 * m + 7) (D := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a + d + 2, 0, 0, d + 1, 0⟩)
  · intro c ⟨a, d, hq⟩; subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      refine ⟨⟨a + 4 * m + 5, 0, 0, 2 * m + 2, 0⟩, ⟨a + 2 * m + 2, 2 * m + 1, ?_⟩, ?_⟩
      · ring_nf
      · show ⟨a + 2 * m + 2, 0, 0, 2 * m + 1, 0⟩ [fm]⊢⁺ ⟨a + 4 * m + 5, 0, 0, 2 * m + 2, 0⟩
        exact main_trans_even m
    · rw [show 2 * m + 1 = 2 * m + 1 from rfl] at hm; subst hm
      refine ⟨⟨a + 4 * m + 7, 0, 0, 2 * m + 3, 0⟩, ⟨a + 2 * m + 3, 2 * m + 2, ?_⟩, ?_⟩
      · ring_nf
      · show ⟨a + 2 * m + 3, 0, 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨a + 4 * m + 7, 0, 0, 2 * m + 3, 0⟩
        exact main_trans_odd m
  · exact ⟨1, 0, rfl⟩
