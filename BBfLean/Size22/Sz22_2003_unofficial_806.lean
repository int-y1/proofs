import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #806: [35/6, 605/2, 8/77, 3/5, 7/3]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 3  0  0 -1 -1
 0  1 -1  0  0
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_806

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem c_to_b : ∀ n b e, ⟨0, b, n, 0, e⟩ [fm]⊢* ⟨0, b + n, 0, 0, e⟩ := by
  intro n; induction n with
  | zero => intro b e; exists 0
  | succ n ih =>
    intro b e
    rw [show b + (n + 1) = (b + 1) + n from by ring]
    step fm
    exact ih (b + 1) e

theorem opening : ∀ b e, ⟨0, b + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨3, b, 0, 0, e⟩ := by
  intro b e; step fm; step fm; finish

theorem mixing : ∀ k b C D E,
    ⟨3, b + 3 * k, C, D, E + k⟩ [fm]⊢* ⟨3, b, C + 3 * k, D + 2 * k, E⟩ := by
  intro k; induction k with
  | zero => intro b C D E; simp; exists 0
  | succ k ih =>
    intro b C D E
    rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show E + (k + 1) = (E + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih b (C + 3) (D + 2) E)
    ring_nf; finish

theorem tail0 : ∀ C D E, ⟨3, 0, C, D, E⟩ [fm]⊢* ⟨0, 0, C + 3, D, E + 6⟩ := by
  intro C D E; step fm; step fm; step fm; finish

theorem tail1 : ∀ C D E, ⟨3, 1, C, D, E⟩ [fm]⊢* ⟨0, 0, C + 3, D + 1, E + 4⟩ := by
  intro C D E; step fm; step fm; step fm; finish

theorem tail2 : ∀ C D E, ⟨3, 2, C, D, E⟩ [fm]⊢* ⟨0, 0, C + 3, D + 2, E + 2⟩ := by
  intro C D E; step fm; step fm; step fm; finish

theorem drain : ∀ D C E, ⟨0, 0, C, D, E + 1⟩ [fm]⊢* ⟨0, 0, C + 3 * D, 0, E + 1 + 5 * D⟩ := by
  intro D; induction D with
  | zero => intro C E; simp; exists 0
  | succ D ih =>
    intro C E
    step fm; step fm; step fm; step fm
    rw [show E + 6 = (E + 5) + 1 from by ring]
    apply stepStar_trans (ih (C + 3) (E + 5))
    ring_nf; finish

theorem trans_mod0 (k E : ℕ) :
    ⟨0, 0, 3 * k + 1, 0, E + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 9 * k + 3, 0, E + 10 * k + 6⟩ := by
  have h1 : ⟨0, 0, 3 * k + 1, 0, E + k + 1⟩ [fm]⊢* ⟨0, 3 * k + 1, 0, 0, E + k + 1⟩ := by
    have := c_to_b (3 * k + 1) 0 (E + k + 1); simpa using this
  have h2 : ⟨0, 3 * k + 1, 0, 0, E + k + 1⟩ [fm]⊢⁺ ⟨3, 3 * k, 0, 0, E + k⟩ := by
    rw [show 3 * k + 1 = (3 * k) + 1 from by ring,
        show E + k + 1 = (E + k) + 1 from by ring]
    exact opening (3 * k) (E + k)
  have h3 : ⟨3, 3 * k, 0, 0, E + k⟩ [fm]⊢* ⟨3, 0, 3 * k, 2 * k, E⟩ := by
    rw [show 3 * k = 0 + 3 * k from by ring]
    have := mixing k 0 0 0 E; simpa using this
  have h4 : ⟨3, 0, 3 * k, 2 * k, E⟩ [fm]⊢* ⟨0, 0, 3 * k + 3, 2 * k, E + 6⟩ :=
    tail0 (3 * k) (2 * k) E
  have h5 : ⟨0, 0, 3 * k + 3, 2 * k, E + 6⟩ [fm]⊢*
      ⟨0, 0, 9 * k + 3, 0, E + 10 * k + 6⟩ := by
    rw [show E + 6 = (E + 5) + 1 from by ring]
    have := drain (2 * k) (3 * k + 3) (E + 5)
    rw [show 3 * k + 3 + 3 * (2 * k) = 9 * k + 3 from by ring,
        show E + 5 + 1 + 5 * (2 * k) = E + 10 * k + 6 from by ring] at this
    exact this
  apply stepStar_stepPlus_stepPlus h1
  apply stepPlus_stepStar_stepPlus h2
  apply stepStar_trans h3
  apply stepStar_trans h4
  exact h5

theorem trans_mod1 (k E : ℕ) :
    ⟨0, 0, 3 * k + 2, 0, E + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 9 * k + 6, 0, E + 10 * k + 9⟩ := by
  have h1 : ⟨0, 0, 3 * k + 2, 0, E + k + 1⟩ [fm]⊢* ⟨0, 3 * k + 2, 0, 0, E + k + 1⟩ := by
    have := c_to_b (3 * k + 2) 0 (E + k + 1); simpa using this
  have h2 : ⟨0, 3 * k + 2, 0, 0, E + k + 1⟩ [fm]⊢⁺ ⟨3, 3 * k + 1, 0, 0, E + k⟩ := by
    rw [show 3 * k + 2 = (3 * k + 1) + 1 from by ring,
        show E + k + 1 = (E + k) + 1 from by ring]
    exact opening (3 * k + 1) (E + k)
  have h3 : ⟨3, 3 * k + 1, 0, 0, E + k⟩ [fm]⊢* ⟨3, 1, 3 * k, 2 * k, E⟩ := by
    rw [show 3 * k + 1 = 1 + 3 * k from by ring]
    have := mixing k 1 0 0 E; simpa using this
  have h4 : ⟨3, 1, 3 * k, 2 * k, E⟩ [fm]⊢* ⟨0, 0, 3 * k + 3, 2 * k + 1, E + 4⟩ :=
    tail1 (3 * k) (2 * k) E
  have h5 : ⟨0, 0, 3 * k + 3, 2 * k + 1, E + 4⟩ [fm]⊢*
      ⟨0, 0, 9 * k + 6, 0, E + 10 * k + 9⟩ := by
    rw [show E + 4 = (E + 3) + 1 from by ring]
    have := drain (2 * k + 1) (3 * k + 3) (E + 3)
    rw [show 3 * k + 3 + 3 * (2 * k + 1) = 9 * k + 6 from by ring,
        show E + 3 + 1 + 5 * (2 * k + 1) = E + 10 * k + 9 from by ring] at this
    exact this
  apply stepStar_stepPlus_stepPlus h1
  apply stepPlus_stepStar_stepPlus h2
  apply stepStar_trans h3
  apply stepStar_trans h4
  exact h5

theorem trans_mod2 (k E : ℕ) :
    ⟨0, 0, 3 * k + 3, 0, E + k + 1⟩ [fm]⊢⁺ ⟨0, 0, 9 * k + 9, 0, E + 10 * k + 12⟩ := by
  have h1 : ⟨0, 0, 3 * k + 3, 0, E + k + 1⟩ [fm]⊢* ⟨0, 3 * k + 3, 0, 0, E + k + 1⟩ := by
    have := c_to_b (3 * k + 3) 0 (E + k + 1); simpa using this
  have h2 : ⟨0, 3 * k + 3, 0, 0, E + k + 1⟩ [fm]⊢⁺ ⟨3, 3 * k + 2, 0, 0, E + k⟩ := by
    rw [show 3 * k + 3 = (3 * k + 2) + 1 from by ring,
        show E + k + 1 = (E + k) + 1 from by ring]
    exact opening (3 * k + 2) (E + k)
  have h3 : ⟨3, 3 * k + 2, 0, 0, E + k⟩ [fm]⊢* ⟨3, 2, 3 * k, 2 * k, E⟩ := by
    rw [show 3 * k + 2 = 2 + 3 * k from by ring]
    have := mixing k 2 0 0 E; simpa using this
  have h4 : ⟨3, 2, 3 * k, 2 * k, E⟩ [fm]⊢* ⟨0, 0, 3 * k + 3, 2 * k + 2, E + 2⟩ :=
    tail2 (3 * k) (2 * k) E
  have h5 : ⟨0, 0, 3 * k + 3, 2 * k + 2, E + 2⟩ [fm]⊢*
      ⟨0, 0, 9 * k + 9, 0, E + 10 * k + 12⟩ := by
    rw [show E + 2 = (E + 1) + 1 from by ring]
    have := drain (2 * k + 2) (3 * k + 3) (E + 1)
    rw [show 3 * k + 3 + 3 * (2 * k + 2) = 9 * k + 9 from by ring,
        show E + 1 + 1 + 5 * (2 * k + 2) = E + 10 * k + 12 from by ring] at this
    exact this
  apply stepStar_stepPlus_stepPlus h1
  apply stepPlus_stepStar_stepPlus h2
  apply stepStar_trans h3
  apply stepStar_trans h4
  exact h5

theorem main_trans (c e : ℕ) (he : e ≥ c) :
    ⟨0, 0, c + 1, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 3 * c + 3, 0, e + 3 * c + 6⟩ := by
  obtain ⟨k, rfl | rfl | rfl⟩ : ∃ k, c = 3 * k ∨ c = 3 * k + 1 ∨ c = 3 * k + 2 := ⟨c / 3, by omega⟩
  · rw [show 3 * (3 * k) + 3 = 9 * k + 3 from by ring,
        show e + 3 * (3 * k) + 6 = e + 9 * k + 6 from by ring,
        show e + 1 = (e - k) + k + 1 from by omega,
        show e + 9 * k + 6 = (e - k) + 10 * k + 6 from by omega]
    exact trans_mod0 k (e - k)
  · rw [show 3 * k + 1 + 1 = 3 * k + 2 from by ring,
        show 3 * (3 * k + 1) + 3 = 9 * k + 6 from by ring,
        show e + 3 * (3 * k + 1) + 6 = e + 9 * k + 9 from by ring,
        show e + 1 = (e - k) + k + 1 from by omega,
        show e + 9 * k + 9 = (e - k) + 10 * k + 9 from by omega]
    exact trans_mod1 k (e - k)
  · rw [show 3 * k + 2 + 1 = 3 * k + 3 from by ring,
        show 3 * (3 * k + 2) + 3 = 9 * k + 9 from by ring,
        show e + 3 * (3 * k + 2) + 6 = e + 9 * k + 12 from by ring,
        show e + 1 = (e - k) + k + 1 from by omega,
        show e + 9 * k + 12 = (e - k) + 10 * k + 12 from by omega]
    exact trans_mod2 k (e - k)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 0, 7⟩)
  · execute fm 7
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c + 1, 0, e + 1⟩ ∧ e ≥ c)
  · intro q ⟨c, e, hq, he⟩; subst hq
    exact ⟨⟨0, 0, 3 * c + 3, 0, e + 3 * c + 6⟩,
      ⟨3 * c + 2, e + 3 * c + 5, rfl, by omega⟩,
      main_trans c e he⟩
  · exact ⟨2, 6, rfl, by omega⟩
