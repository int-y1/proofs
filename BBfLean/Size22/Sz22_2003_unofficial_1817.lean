import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1817: [9/10, 55/21, 4/3, 49/11, 33/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 2 -1  0  0  0
 0  0  0  2 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1817

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

theorem r2r1_chain : ∀ k, ⟨a + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a := a) (b := b + 1) (d := d) (e := e + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ⟨0, b + k, c, d + k, e⟩ [fm]⊢* ⟨0, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (c := c + 1) (d := d) (e := e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a := a + 2))
    ring_nf; finish

theorem endgame : ∀ C, ∀ B e, ⟨0, B + 1, C, 0, e⟩ [fm]⊢* ⟨2 * B + 3 * C + 2, 0, 0, 0, e⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro B e
  rcases C with _ | _ | C
  · apply stepStar_trans (r3_chain (B + 1) (a := 0))
    ring_nf; finish
  · step fm; step fm; step fm
    apply stepStar_trans (r3_chain (B + 1) (a := 3))
    ring_nf; finish
  · step fm; step fm; step fm
    show ⟨0, B + 3 + 1, C, 0, e⟩ [fm]⊢* _
    apply stepStar_trans (ih C (by omega) (B + 3) e)
    ring_nf; finish

theorem main_trans (A F : ℕ) :
    ⟨2 * A + F + 1, 0, 0, 0, A + F⟩ [fm]⊢⁺
    ⟨2 * (2 * A + F) + (F + 1) + 1, 0, 0, 0, (2 * A + F) + (F + 1)⟩ := by
  rw [show (A + F : ℕ) = 0 + (A + F) from by ring]
  apply stepStar_stepPlus_stepPlus
    (e_to_d (A + F) (a := 2 * A + F + 1) (d := 0) (e := 0))
  rw [show 2 * A + F + 1 = (2 * A + F) + 1 from by ring,
      show 0 + 2 * (A + F) = 2 * A + 2 * F from by ring]
  step fm
  have phase3 : ⟨2 * A + F, 1, 0, 2 * A + 2 * F, 1⟩ [fm]⊢*
      ⟨0, 2 * A + F + 1, 0, F, 2 * A + F + 1⟩ := by
    have := r2r1_chain (2 * A + F) (a := 0) (b := 0) (d := F) (e := 1)
    simp only [Nat.zero_add] at this
    rw [show F + (2 * A + F) = 2 * A + 2 * F from by ring,
        show 1 + (2 * A + F) = 2 * A + F + 1 from by ring] at this
    exact this
  have phase4 : ⟨0, 2 * A + F + 1, 0, F, 2 * A + F + 1⟩ [fm]⊢*
      ⟨0, 2 * A + 1, F, 0, 2 * A + 2 * F + 1⟩ := by
    have := r2_drain F (b := 2 * A + 1) (c := 0) (d := 0) (e := 2 * A + F + 1)
    simp only [Nat.zero_add] at this
    rw [show 2 * A + 1 + F = 2 * A + F + 1 from by ring,
        show 2 * A + F + 1 + F = 2 * A + 2 * F + 1 from by ring] at this
    exact this
  apply stepStar_trans phase3
  apply stepStar_trans phase4
  apply stepStar_trans (endgame F (2 * A) (2 * A + 2 * F + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, F⟩ ↦ ⟨2 * A + F + 1, 0, 0, 0, A + F⟩) ⟨0, 1⟩
  intro ⟨A, F⟩; exact ⟨⟨2 * A + F, F + 1⟩, main_trans A F⟩
