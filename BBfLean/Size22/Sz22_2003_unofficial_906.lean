import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #906: [4/15, 3/14, 275/2, 7/5, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_906

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ a c e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * a, 0, e + a⟩ := by
  intro a; induction a with
  | zero => intros; exists 0
  | succ a ih =>
    intro c e
    step fm
    apply stepStar_trans (ih (c + 2) (e + 1))
    ring_nf; finish

theorem c_to_d : ∀ c d e, ⟨0, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + c, e⟩ := by
  intro c; induction c with
  | zero => intros; exists 0
  | succ c ih =>
    intro d e
    rw [show d + (c + 1) = (d + 1) + c from by ring]
    step fm
    exact ih (d + 1) e

theorem drain : ∀ m A F,
    ⟨A + 1, 2 * m + 1, 0, 0, F⟩ [fm]⊢* ⟨A + 3 * m + 2, 0, 1, 0, F + m + 1⟩ := by
  intro m; induction m with
  | zero =>
    intro A F
    show ⟨A + 1, 1, 0, 0, F⟩ [fm]⊢* ⟨A + 2, 0, 1, 0, F + 1⟩
    step fm
    step fm
    finish
  | succ m ih =>
    intro A F
    show ⟨A + 1, 2 * m + 3, 0, 0, F⟩ [fm]⊢* ⟨A + 3 * m + 5, 0, 1, 0, F + m + 2⟩
    rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
    step fm
    show ⟨A, (2 * m + 1) + 1 + 1, 2, 0, F + 1⟩ [fm]⊢* ⟨A + 3 * m + 5, 0, 1, 0, F + m + 2⟩
    step fm
    show ⟨A + 2, (2 * m + 1) + 1, 1, 0, F + 1⟩ [fm]⊢* ⟨A + 3 * m + 5, 0, 1, 0, F + m + 2⟩
    rw [show A + 2 = (A + 1) + 1 from by ring]
    step fm
    show ⟨A + 1 + 1 + 2, 2 * m + 1, 0, 0, F + 1⟩ [fm]⊢* ⟨A + 3 * m + 5, 0, 1, 0, F + m + 2⟩
    rw [show A + 1 + 1 + 2 = (A + 3) + 1 from by ring]
    apply stepStar_trans (ih (A + 3) (F + 1))
    ring_nf; finish

theorem round0 : ∀ D E, ⟨0, 0, 0, D + 3, E + 1⟩ [fm]⊢* ⟨0, 2, 0, D, E⟩ := by
  intro D E
  show ⟨0, 0, 0, (D + 2) + 1, E + 1⟩ [fm]⊢* ⟨0, 2, 0, D, E⟩
  step fm
  show ⟨1, 0, 1, (D + 2) + 1, E⟩ [fm]⊢* ⟨0, 2, 0, D, E⟩
  rw [show (1 : ℕ) = 0 + 1 from rfl, show (D + 2) + 1 = (D + 1) + 1 + 1 from by ring]
  step fm
  show ⟨0, 1, 1, (D + 1) + 1, E⟩ [fm]⊢* ⟨0, 2, 0, D, E⟩
  step fm
  show ⟨2, 0, 0, (D + 1) + 1, E⟩ [fm]⊢* ⟨0, 2, 0, D, E⟩
  rw [show (2 : ℕ) = 0 + 1 + 1 from rfl]
  step fm
  show ⟨0 + 1, 1, 0, D + 1, E⟩ [fm]⊢* ⟨0, 2, 0, D, E⟩
  step fm
  show ⟨0, 2, 0, D, E⟩ [fm]⊢* ⟨0, 2, 0, D, E⟩
  finish

theorem roundS : ∀ B D E, ⟨0, B + 1, 0, D + 3, E + 1⟩ [fm]⊢* ⟨0, B + 3, 0, D, E⟩ := by
  intro B D E
  show ⟨0, B + 1, 0, (D + 2) + 1, E + 1⟩ [fm]⊢* ⟨0, B + 3, 0, D, E⟩
  step fm
  show ⟨1, B + 1, 1, (D + 2) + 1, E⟩ [fm]⊢* ⟨0, B + 3, 0, D, E⟩
  step fm
  show ⟨3, B, 0, (D + 2) + 1, E⟩ [fm]⊢* ⟨0, B + 3, 0, D, E⟩
  rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl, show (D + 2) + 1 = (D + 1) + 1 + 1 from by ring]
  step fm
  show ⟨0 + 1 + 1, B + 1, 0, (D + 1) + 1, E⟩ [fm]⊢* ⟨0, B + 3, 0, D, E⟩
  step fm
  show ⟨0 + 1, B + 1 + 1, 0, D + 1, E⟩ [fm]⊢* ⟨0, B + 3, 0, D, E⟩
  step fm
  show ⟨0, B + 1 + 1 + 1, 0, D, E⟩ [fm]⊢* ⟨0, B + 3, 0, D, E⟩
  rw [show B + 1 + 1 + 1 = B + 3 from by ring]
  finish

theorem gen_rounds : ∀ k b E,
    ⟨0, b, 0, 3 * k + 2, E + k + 1⟩ [fm]⊢* ⟨1, b + 2 * k + 1, 0, 0, E⟩ := by
  intro k; induction k with
  | zero =>
    intro b E
    show ⟨0, b, 0, 2, E + 1⟩ [fm]⊢* ⟨1, b + 1, 0, 0, E⟩
    rcases b with _ | b
    · show ⟨0, 0, 0, 2, E + 1⟩ [fm]⊢* ⟨1, 1, 0, 0, E⟩
      rw [show (2 : ℕ) = 0 + 1 + 1 from rfl]
      step fm
      show ⟨1, 0, 1, 0 + 1 + 1, E⟩ [fm]⊢* ⟨1, 1, 0, 0, E⟩
      rw [show (1 : ℕ) = 0 + 1 from rfl]
      step fm
      show ⟨0, 1, 1, 0 + 1, E⟩ [fm]⊢* ⟨1, 1, 0, 0, E⟩
      step fm
      show ⟨2, 0, 0, 0 + 1, E⟩ [fm]⊢* ⟨1, 1, 0, 0, E⟩
      rw [show (2 : ℕ) = 0 + 1 + 1 from rfl]
      step fm
      finish
    · show ⟨0, b + 1, 0, 2, E + 1⟩ [fm]⊢* ⟨1, b + 2, 0, 0, E⟩
      rw [show (2 : ℕ) = 0 + 1 + 1 from rfl]
      step fm
      show ⟨1, b + 1, 1, 0 + 1 + 1, E⟩ [fm]⊢* ⟨1, b + 2, 0, 0, E⟩
      step fm
      show ⟨3, b, 0, 0 + 1 + 1, E⟩ [fm]⊢* ⟨1, b + 2, 0, 0, E⟩
      rw [show (3 : ℕ) = 0 + 1 + 1 + 1 from rfl]
      step fm
      show ⟨0 + 1 + 1, b + 1, 0, 0 + 1, E⟩ [fm]⊢* ⟨1, b + 2, 0, 0, E⟩
      step fm
      show ⟨0 + 1, b + 1 + 1, 0, 0, E⟩ [fm]⊢* ⟨1, b + 2, 0, 0, E⟩
      rw [show b + 1 + 1 = b + 2 from by ring, show (0 : ℕ) + 1 = 1 from rfl]
      finish
  | succ k ih =>
    intro b E
    show ⟨0, b, 0, 3 * k + 5, E + k + 2⟩ [fm]⊢* ⟨1, b + 2 * k + 3, 0, 0, E⟩
    rw [show 3 * k + 5 = (3 * k + 2) + 3 from by ring,
        show E + k + 2 = (E + k + 1) + 1 from by ring]
    rcases b with _ | b
    · apply stepStar_trans (round0 (3 * k + 2) (E + k + 1))
      apply stepStar_trans (ih 2 E)
      rw [show 2 + 2 * k + 1 = 0 + 2 * k + 3 from by ring]
      finish
    · apply stepStar_trans (roundS b (3 * k + 2) (E + k + 1))
      apply stepStar_trans (ih (b + 3) E)
      rw [show b + 3 + 2 * k + 1 = b + 1 + 2 * k + 3 from by ring]
      finish

theorem spiral (k E : ℕ) :
    ⟨0, 0, 0, 3 * k + 2, E + k + 1⟩ [fm]⊢* ⟨3 * k + 2, 0, 1, 0, E + k + 1⟩ := by
  apply stepStar_trans (gen_rounds k 0 E)
  show ⟨1, 0 + 2 * k + 1, 0, 0, E⟩ [fm]⊢* ⟨3 * k + 2, 0, 1, 0, E + k + 1⟩
  rw [show 0 + 2 * k + 1 = 2 * k + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (drain k 0 E)
  ring_nf; finish

theorem main_trans (n e : ℕ) :
    ⟨3 * n + 2, 0, 1, 0, e⟩ [fm]⊢⁺ ⟨6 * n + 5, 0, 1, 0, e + 3 * n + 2⟩ := by
  rw [show 3 * n + 2 = (3 * n + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (r3_chain (3 * n + 1) 3 (e + 1))
  rw [show 3 + 2 * (3 * n + 1) = 6 * n + 5 from by ring,
      show e + 1 + (3 * n + 1) = e + 3 * n + 2 from by ring]
  apply stepStar_trans (c_to_d (6 * n + 5) 0 (e + 3 * n + 2))
  rw [show 0 + (6 * n + 5) = 6 * n + 5 from by ring,
      show 6 * n + 5 = 3 * (2 * n + 1) + 2 from by ring,
      show e + 3 * n + 2 = (e + n) + (2 * n + 1) + 1 from by ring]
  apply stepStar_trans (spiral (2 * n + 1) (e + n))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 1⟩)
  · execute fm 9
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨3 * n + 2, 0, 1, 0, e⟩)
  · intro c ⟨n, e, hq⟩; subst hq
    exact ⟨⟨6 * n + 5, 0, 1, 0, e + 3 * n + 2⟩,
      ⟨2 * n + 1, e + 3 * n + 2, by ring_nf⟩, main_trans n e⟩
  · exact ⟨0, 1, rfl⟩
