import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1980: [99/35, 26/5, 25/39, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  1  0
 1  0 -1  0  0  1
 0 -1  2  0  0 -1
 0  0  0  1 -1  0
-1  0  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1980

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+2, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k, f⟩ [fm]⊢* ⟨(a : ℕ), 0, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih generalizing a d f
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem drain : ∀ b, ⟨a, b, 0, 0, e, f + 1⟩ [fm]⊢* ⟨a + 2 * b, 0, 0, 0, e, f + b + 1⟩ := by
  intro b; induction' b with b ih generalizing a e f
  · exists 0
  · step fm; step fm; step fm
    rw [show f + 1 + 1 = (f + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 2) (f := f + 1))
    ring_nf; finish

theorem r3r1r1_even : ∀ k, ∀ B E F,
    ⟨a, B + 1, 0, 2 * k, E, F + k⟩ [fm]⊢* ⟨(a : ℕ), B + 3 * k + 1, 0, 0, E + 2 * k, F⟩ := by
  intro k; induction' k with k ih
  · intro B E F; exists 0
  · intro B E F
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring,
        show F + (k + 1) = (F + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (B + 3) (E + 2) F)
    ring_nf; finish

theorem r3r1r1_odd : ∀ k, ∀ B E F,
    ⟨a, B + 1, 0, 2 * k + 1, E, F + k + 1⟩ [fm]⊢*
    ⟨(a : ℕ), B + 3 * k + 1, 0, 1, E + 2 * k, F + 1⟩ := by
  intro k; induction' k with k ih
  · intro B E F; exists 0
  · intro B E F
    rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show F + (k + 1) + 1 = (F + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show E + 1 + 1 = E + 2 from by ring]
    apply stepStar_trans (ih (B + 3) (E + 2) F)
    ring_nf; finish

theorem r3r1r2 : ⟨a, B + 1, 0, 1, E, F + 1⟩ [fm]⊢⁺ ⟨a + 1, B + 2, 0, 0, E + 1, F + 1⟩ := by
  step fm; step fm; step fm; finish

theorem main_trans_odd (k : ℕ) : ⟨a + 1, 0, 0, 2 * k + 1, 0, 2 * k + G + 1⟩ [fm]⊢⁺
    ⟨a + 6 * k + 4, 0, 0, 2 * k + 2, 0, 4 * k + G + 3⟩ := by
  step fm; step fm
  rw [show (1 + 1 : ℕ) * k = 2 * k from by ring,
      show 2 * k + G + 1 = (k + G + 1) + k from by ring]
  show ⟨a, 1 + 1, 0, 2 * k, 2, (k + G + 1) + k⟩ [fm]⊢* _
  apply stepStar_trans (r3r1r1_even k 1 2 (k + G + 1) (a := a))
  rw [show 1 + 3 * k + 1 = 3 * k + 2 from by ring,
      show 2 + 2 * k = 2 * k + 2 from by ring,
      show k + G + 1 = (k + G) + 1 from by ring]
  apply stepStar_trans (drain (3 * k + 2) (a := a) (e := 2 * k + 2) (f := k + G))
  rw [show a + 2 * (3 * k + 2) = a + 6 * k + 4 from by ring,
      show k + G + (3 * k + 2) + 1 = 4 * k + G + 3 from by ring]
  have h := e_to_d (2 * k + 2) (a := a + 6 * k + 4) (d := 0) (f := 4 * k + G + 3)
  simp at h; exact h

theorem main_trans_even (k : ℕ) : ⟨a + 1, 0, 0, 2 * k + 2, 0, 2 * k + G + 2⟩ [fm]⊢⁺
    ⟨a + 6 * k + 7, 0, 0, 2 * k + 3, 0, 4 * k + G + 5⟩ := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm; step fm
  rw [show (1 + 1 : ℕ) * k + 1 = 2 * k + 1 from by ring,
      show 2 * k + G + 2 = (k + G + 1) + k + 1 from by ring]
  show ⟨a, 1 + 1, 0, 2 * k + 1, 2, (k + G + 1) + k + 1⟩ [fm]⊢* _
  apply stepStar_trans (r3r1r1_odd k 1 2 (k + G + 1) (a := a))
  rw [show 1 + 3 * k + 1 = (3 * k + 1) + 1 from by ring,
      show 2 + 2 * k = 2 * k + 2 from by ring,
      show k + G + 1 + 1 = (k + G + 1) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (r3r1r2 (a := a) (B := 3 * k + 1) (E := 2 * k + 2) (F := k + G + 1)))
  rw [show 3 * k + 1 + 2 = 3 * k + 3 from by ring,
      show 2 * k + 2 + 1 = 2 * k + 3 from by ring,
      show k + G + 1 + 1 = (k + G + 1) + 1 from by ring]
  apply stepStar_trans (drain (3 * k + 3) (a := a + 1) (e := 2 * k + 3) (f := k + G + 1))
  rw [show a + 1 + 2 * (3 * k + 3) = a + 6 * k + 7 from by ring,
      show k + G + 1 + (3 * k + 3) + 1 = 4 * k + G + 5 from by ring]
  have h := e_to_d (2 * k + 3) (a := a + 6 * k + 7) (d := 0) (f := 4 * k + G + 5)
  simp at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 0, 1⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d G, q = ⟨a + 1, 0, 0, d + 1, 0, d + G + 1⟩)
  · intro c ⟨a, d, G, hq⟩; subst hq
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show k + k = 2 * k from by ring] at hk; subst hk
      refine ⟨⟨a + 6 * k + 4, 0, 0, 2 * k + 2, 0, 4 * k + G + 3⟩,
        ⟨a + 6 * k + 3, 2 * k + 1, 2 * k + G + 1, by ring_nf⟩, ?_⟩
      rw [show 2 * k + G + 1 = 2 * k + G + 1 from rfl]
      exact main_trans_odd k
    · subst hk
      refine ⟨⟨a + 6 * k + 7, 0, 0, 2 * k + 3, 0, 4 * k + G + 5⟩,
        ⟨a + 6 * k + 6, 2 * k + 2, 2 * k + G + 2, by ring_nf⟩, ?_⟩
      rw [show 2 * k + 1 + G + 1 = 2 * k + G + 2 from by ring]
      exact main_trans_even k
  · exact ⟨0, 0, 0, rfl⟩
