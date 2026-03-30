import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #655: [35/6, 1573/2, 4/55, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  2  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_655

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

theorem d_to_b : ∀ k, ⟨0, b, 0, 0 + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih generalizing b
  · exists 0
  · rw [Nat.add_succ 0 k]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem drain : ∀ k, ⟨0, 0, k, D, e + 1, f⟩ [fm]⊢* ⟨0, 0, 0, D, e + 1 + 3 * k, f + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing e f
  · exists 0
  · step fm
    step fm
    step fm
    show ⟨0, 0, k, D, e + 4, f + 2⟩ [fm]⊢* ⟨0, 0, 0, D, e + 1 + 3 * (k + 1), f + 2 * (k + 1)⟩
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (e := e + 3) (f := f + 2))
    ring_nf; finish

theorem main_loop :
    ∀ b, ∀ c D F, ∀ e, e ≥ b →
    ⟨1, b, c, D, e + 1, F⟩ [fm]⊢* ⟨0, 0, 0, D + b, e + 1 + b + 2 + 3 * c, F + b + 1 + 2 * c⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  intro c D F e he
  rcases b with _ | _ | b
  · step fm
    show ⟨0, 0, c, D, e + 3, F + 1⟩ [fm]⊢* _
    rw [show e + 3 = (e + 2) + 1 from by ring]
    apply stepStar_trans (drain c (D := D) (e := e + 2) (f := F + 1))
    ring_nf; finish
  · step fm
    step fm
    step fm
    step fm
    show ⟨0, 0, c, D + 1, e + 4, F + 2⟩ [fm]⊢* _
    rw [show e + 4 = (e + 3) + 1 from by ring]
    apply stepStar_trans (drain c (D := D + 1) (e := e + 3) (f := F + 2))
    ring_nf; finish
  · step fm
    step fm
    show ⟨2, b + 1, c, D + 1, e, F⟩ [fm]⊢* _
    step fm
    show ⟨1, b, c + 1, D + 2, e, F⟩ [fm]⊢* _
    rw [show e = (e - 1) + 1 from by omega]
    apply stepStar_trans (ih b (by omega) (c + 1) (D + 2) F (e - 1) (by omega))
    have : e - 1 + 1 = e := by omega
    rw [this]; ring_nf; finish

theorem main_trans (he : e ≥ 2 * d + 2) :
    ⟨0, 0, 0, d + 1, e + 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2, e + d + 4, f + d + 2⟩ := by
  rw [show (d + 1 : ℕ) = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact d_to_b (d + 1) (b := 0) (e := e + 1) (f := f + 1)
  simp only [Nat.zero_add]
  step fm
  show ⟨1, d + 1, 0, 1, e + 1, f⟩ [fm]⊢* ⟨0, 0, 0, d + 2, e + d + 4, f + d + 2⟩
  apply stepStar_trans (main_loop (d + 1) 0 1 f e (by omega))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 4, 1⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e f, q = ⟨0, 0, 0, d + 1, e + 1, f + 1⟩ ∧ e = f + 2 * d + 3 ∧ e ≥ 2 * d + 2)
  · intro c ⟨d, e, f, hq, hinv, hge⟩; subst hq
    exact ⟨⟨0, 0, 0, d + 2, e + d + 4, f + d + 2⟩,
      ⟨d + 1, e + d + 3, f + d + 1, rfl, by omega, by omega⟩,
      main_trans hge⟩
  · exact ⟨0, 3, 0, rfl, by omega, by omega⟩
