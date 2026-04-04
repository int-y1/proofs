import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1862: [9/35, 22/5, 25/33, 7/11, 605/2]

Vector representation:
```
 0  2 -1 -1  0
 1  0 -1  0  1
 0 -1  2  0 -1
 0  0  0  1 -1
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1862

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (d + 1))
    rw [show d + 1 + k = d + (k + 1) from by omega]; finish

theorem big_round : ⟨a + 1, b, 0, d + 5, 0⟩ [fm]⊢* ⟨a, b + 8, 0, d, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem big_round_chain : ∀ k, ∀ a b d, ⟨a + k, b, 0, d + 5 * k, 0⟩ [fm]⊢* ⟨a, b + 8 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by omega,
        show d + 5 * (k + 1) = (d + 5) + 5 * k from by omega]
    apply stepStar_trans (ih (a + 1) b (d + 5))
    apply stepStar_trans (big_round (a := a) (b := b + 8 * k) (d := d))
    rw [show b + 8 * k + 8 = b + 8 * (k + 1) from by omega]; finish

theorem b_drain : ∀ B a e, ⟨a, B, 0, 0, e + 1⟩ [fm]⊢* ⟨a + 2 * B, 0, 0, 0, e + B + 1⟩ := by
  intro B; induction' B with B ih <;> intro a e
  · exists 0
  · step fm; step fm; step fm
    show ⟨a + 1 + 1, B, 0, 0, (e + 1) + 1⟩ [fm]⊢* ⟨a + 2 * (B + 1), 0, 0, 0, e + (B + 1) + 1⟩
    apply stepStar_trans (ih (a + 2) (e + 1))
    rw [show a + 2 + 2 * B = a + 2 * (B + 1) from by omega,
        show e + 1 + B + 1 = e + (B + 1) + 1 from by omega]; finish

theorem rem0 : ⟨A + 1, B, 0, 0, 0⟩ [fm]⊢⁺ ⟨A + 2 * B + 1, 0, 0, 0, B + 3⟩ := by
  step fm; step fm
  show ⟨A + 1, B, 0, 0, 2 + 1⟩ [fm]⊢* ⟨A + 2 * B + 1, 0, 0, 0, B + 3⟩
  apply stepStar_trans (b_drain B (A + 1) 2)
  rw [show A + 1 + 2 * B = A + 2 * B + 1 from by omega,
      show 2 + B + 1 = B + 3 from by omega]; finish

theorem rem1 : ⟨A + 1, B, 0, 1, 0⟩ [fm]⊢⁺ ⟨A + 2 * B + 4, 0, 0, 0, B + 4⟩ := by
  step fm; step fm; step fm; step fm; step fm
  show ⟨A + 1 + 1, B + 1, 0, 0, 2 + 1⟩ [fm]⊢* ⟨A + 2 * B + 4, 0, 0, 0, B + 4⟩
  apply stepStar_trans (b_drain (B + 1) (A + 2) 2)
  rw [show A + 2 + 2 * (B + 1) = A + 2 * B + 4 from by omega,
      show 2 + (B + 1) + 1 = B + 4 from by omega]; finish

theorem rem2 : ⟨A + 1, B, 0, 2, 0⟩ [fm]⊢⁺ ⟨A + 2 * B + 7, 0, 0, 0, B + 5⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨A + 1 + 1 + 1, B + 2, 0, 0, 2 + 1⟩ [fm]⊢* ⟨A + 2 * B + 7, 0, 0, 0, B + 5⟩
  apply stepStar_trans (b_drain (B + 2) (A + 3) 2)
  rw [show A + 3 + 2 * (B + 2) = A + 2 * B + 7 from by omega,
      show 2 + (B + 2) + 1 = B + 5 from by omega]; finish

theorem rem3 : ⟨A + 1, B, 0, 3, 0⟩ [fm]⊢⁺ ⟨A + 2 * B + 10, 0, 0, 0, B + 6⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm
  show ⟨A + 1 + 1 + 1 + 1, B + 3, 0, 0, 2 + 1⟩ [fm]⊢* ⟨A + 2 * B + 10, 0, 0, 0, B + 6⟩
  apply stepStar_trans (b_drain (B + 3) (A + 4) 2)
  rw [show A + 4 + 2 * (B + 3) = A + 2 * B + 10 from by omega,
      show 2 + (B + 3) + 1 = B + 6 from by omega]; finish

theorem rem4 : ⟨A + 1, B, 0, 4, 0⟩ [fm]⊢⁺ ⟨A + 2 * B + 13, 0, 0, 0, B + 7⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨A + 1 + 1 + 1 + 1 + 1, B + 4, 0, 0, 2 + 1⟩ [fm]⊢* ⟨A + 2 * B + 13, 0, 0, 0, B + 7⟩
  apply stepStar_trans (b_drain (B + 4) (A + 5) 2)
  rw [show A + 5 + 2 * (B + 4) = A + 2 * B + 13 from by omega,
      show 2 + (B + 4) + 1 = B + 7 from by omega]; finish

theorem main_r0 : ⟨A + q + 1, 0, 0, 0, 5 * q⟩ [fm]⊢⁺ ⟨A + 16 * q + 1, 0, 0, 0, 8 * q + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show (5 * q : ℕ) = 0 + 5 * q from by omega]
    apply stepStar_trans (e_to_d (5 * q) 0 (a := A + q + 1) (e := 0))
    rw [show A + q + 1 = (A + 1) + q from by omega]
    apply stepStar_trans (big_round_chain q 0 (a := A + 1) (b := 0))
    rw [show 0 + 8 * q = 8 * q from by omega]; finish
  · rw [show A + 16 * q + 1 = A + 2 * (8 * q) + 1 from by omega]
    exact rem0

theorem main_r1 : ⟨A + q + 1, 0, 0, 0, 5 * q + 1⟩ [fm]⊢⁺ ⟨A + 16 * q + 4, 0, 0, 0, 8 * q + 4⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 5 * q + 1 = 0 + (5 * q + 1) from by omega]
    apply stepStar_trans (e_to_d (5 * q + 1) 0 (a := A + q + 1) (e := 0))
    rw [show 0 + (5 * q + 1) = 1 + 5 * q from by omega,
        show A + q + 1 = (A + 1) + q from by omega]
    apply stepStar_trans (big_round_chain q 1 (a := A + 1) (b := 0))
    rw [show 0 + 8 * q = 8 * q from by omega]; finish
  · rw [show A + 16 * q + 4 = A + 2 * (8 * q) + 4 from by omega]
    exact rem1

theorem main_r2 : ⟨A + q + 1, 0, 0, 0, 5 * q + 2⟩ [fm]⊢⁺ ⟨A + 16 * q + 7, 0, 0, 0, 8 * q + 5⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 5 * q + 2 = 0 + (5 * q + 2) from by omega]
    apply stepStar_trans (e_to_d (5 * q + 2) 0 (a := A + q + 1) (e := 0))
    rw [show 0 + (5 * q + 2) = 2 + 5 * q from by omega,
        show A + q + 1 = (A + 1) + q from by omega]
    apply stepStar_trans (big_round_chain q 2 (a := A + 1) (b := 0))
    rw [show 0 + 8 * q = 8 * q from by omega]; finish
  · rw [show A + 16 * q + 7 = A + 2 * (8 * q) + 7 from by omega]
    exact rem2

theorem main_r3 : ⟨A + q + 1, 0, 0, 0, 5 * q + 3⟩ [fm]⊢⁺ ⟨A + 16 * q + 10, 0, 0, 0, 8 * q + 6⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 5 * q + 3 = 0 + (5 * q + 3) from by omega]
    apply stepStar_trans (e_to_d (5 * q + 3) 0 (a := A + q + 1) (e := 0))
    rw [show 0 + (5 * q + 3) = 3 + 5 * q from by omega,
        show A + q + 1 = (A + 1) + q from by omega]
    apply stepStar_trans (big_round_chain q 3 (a := A + 1) (b := 0))
    rw [show 0 + 8 * q = 8 * q from by omega]; finish
  · rw [show A + 16 * q + 10 = A + 2 * (8 * q) + 10 from by omega]
    exact rem3

theorem main_r4 : ⟨A + q + 1, 0, 0, 0, 5 * q + 4⟩ [fm]⊢⁺ ⟨A + 16 * q + 13, 0, 0, 0, 8 * q + 7⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 5 * q + 4 = 0 + (5 * q + 4) from by omega]
    apply stepStar_trans (e_to_d (5 * q + 4) 0 (a := A + q + 1) (e := 0))
    rw [show 0 + (5 * q + 4) = 4 + 5 * q from by omega,
        show A + q + 1 = (A + 1) + q from by omega]
    apply stepStar_trans (big_round_chain q 4 (a := A + 1) (b := 0))
    rw [show 0 + 8 * q = 8 * q from by omega]; finish
  · rw [show A + 16 * q + 13 = A + 2 * (8 * q) + 13 from by omega]
    exact rem4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨10, 0, 0, 0, 6⟩) (by execute fm 25)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ e ∧ e ≥ 3)
  · intro c ⟨a, e, hq, ha, he⟩; subst hq
    obtain ⟨q, r, hr, hlr⟩ : ∃ q r, e = 5 * q + r ∧ r < 5 := ⟨e / 5, e % 5, by omega, by omega⟩
    subst hr
    obtain ⟨A, rfl⟩ : ∃ A, a = A + q + 1 := ⟨a - q - 1, by omega⟩
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 from by omega) with
      rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, ⟨A + 16 * q + 1, 8 * q + 3, rfl, by omega, by omega⟩, main_r0⟩
    · exact ⟨_, ⟨A + 16 * q + 4, 8 * q + 4, rfl, by omega, by omega⟩, main_r1⟩
    · exact ⟨_, ⟨A + 16 * q + 7, 8 * q + 5, rfl, by omega, by omega⟩, main_r2⟩
    · exact ⟨_, ⟨A + 16 * q + 10, 8 * q + 6, rfl, by omega, by omega⟩, main_r3⟩
    · exact ⟨_, ⟨A + 16 * q + 13, 8 * q + 7, rfl, by omega, by omega⟩, main_r4⟩
  · exact ⟨10, 6, rfl, by omega, by omega⟩
