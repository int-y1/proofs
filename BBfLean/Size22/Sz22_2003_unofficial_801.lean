import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #801: [35/6, 605/2, 4/77, 3/5, 7/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_801

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem c_to_b : ∀ k, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem r1r1r3_loop : ∀ k, ∀ b C D E,
    ⟨2, b + 2 * k, C, D, E + k⟩ [fm]⊢* ⟨2, b, C + 2 * k, D + k, E⟩ := by
  intro k; induction' k with k ih <;> intro b C D E
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm
    step fm
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (C + 2) (D + 1) E)
    ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ C D E,
    ⟨0, 0, C, D + k, E + 1⟩ [fm]⊢* ⟨0, 0, C + 2 * k, D, E + 3 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring,
        show E + 1 = E + 0 + 1 from by ring]
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (C + 2) D (E + 3))
    ring_nf; finish

theorem main_odd (k n : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, 2 * k + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 4 * k + 2, 0, 4 * k + n + 5⟩ := by
  have h1 : ⟨0, 0, 0 + (2 * k + 1), 0, 2 * k + n + 2⟩ [fm]⊢*
      ⟨0, 0 + (2 * k + 1), 0, 0, 2 * k + n + 2⟩ :=
    c_to_b (2 * k + 1) (b := 0) (c := 0) (e := 2 * k + n + 2)
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  step fm
  rw [show 2 * k + n + 2 = (2 * k + n + 1) + 1 from by ring]
  step fm
  rw [show 2 * k + n + 1 = (k + n + 1) + k from by ring,
      show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (r1r1r3_loop k 0 0 0 (k + n + 1))
  step fm
  step fm
  rw [show 0 + 2 * k + 1 + 1 = 2 * k + 2 from by ring,
      show 0 + k = 0 + k from rfl,
      show k + n + 1 + 2 + 2 = (k + n + 4) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain k (2 * k + 2) 0 (k + n + 4))
  ring_nf; finish

theorem main_even (k n : ℕ) :
    ⟨0, 0, 2 * k + 2, 0, 2 * k + n + 3⟩ [fm]⊢⁺ ⟨0, 0, 4 * k + 4, 0, 4 * k + n + 7⟩ := by
  have h1 : ⟨0, 0, 0 + (2 * k + 2), 0, 2 * k + n + 3⟩ [fm]⊢*
      ⟨0, 0 + (2 * k + 2), 0, 0, 2 * k + n + 3⟩ :=
    c_to_b (2 * k + 2) (b := 0) (c := 0) (e := 2 * k + n + 3)
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  rw [show 2 * k + n + 3 = (2 * k + n + 2) + 1 from by ring]
  step fm
  rw [show 2 * k + 1 = 1 + 2 * k from by ring,
      show 2 * k + n + 2 = (k + n + 2) + k from by ring]
  apply stepStar_trans (r1r1r3_loop k 1 0 0 (k + n + 2))
  step fm
  step fm
  rw [show 0 + 2 * k + 1 + 1 = 2 * k + 2 from by ring,
      show 0 + k + 1 = 0 + (k + 1) from by ring,
      show k + n + 2 + 2 = (k + n + 3) + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) (2 * k + 2) 0 (k + n + 3))
  ring_nf; finish

theorem main_trans (c n : ℕ) :
    ⟨0, 0, c + 1, 0, c + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 2, 0, 2 * c + n + 5⟩ := by
  rcases Nat.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    rw [show 2 * (2 * k) + 2 = 4 * k + 2 from by ring,
        show 2 * (2 * k) + n + 5 = 4 * k + n + 5 from by ring]
    exact main_odd k n
  · subst hk
    rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
        show 2 * k + 1 + n + 2 = 2 * k + n + 3 from by ring,
        show 2 * (2 * k + 1) + 2 = 4 * k + 4 from by ring,
        show 2 * (2 * k + 1) + n + 5 = 4 * k + n + 7 from by ring]
    exact main_even k n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, p.1 + 1, 0, p.1 + p.2 + 2⟩) ⟨0, 0⟩
  intro ⟨c, n⟩
  refine ⟨⟨2 * c + 1, n + 2⟩, ?_⟩
  show ⟨0, 0, c + 1, 0, c + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 1 + 1, 0, 2 * c + 1 + (n + 2) + 2⟩
  rw [show 2 * c + 1 + 1 = 2 * c + 2 from by ring,
      show 2 * c + 1 + (n + 2) + 2 = 2 * c + n + 5 from by ring]
  exact main_trans c n
