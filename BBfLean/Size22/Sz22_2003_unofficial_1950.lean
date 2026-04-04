import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1950: [9/70, 55/2, 4/33, 7/11, 33/5]

Vector representation:
```
-1  2 -1 -1  0
-1  0  1  0  1
 2 -1  0  0 -1
 0  0  0  1 -1
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1950

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih (d := d + 1)

theorem drain_round : ⟨0, b, c + 3, d + 2, 0⟩ [fm]⊢* ⟨0, b + 4, c, d, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem drain_loop : ∀ k, ⟨0, b, c + 3 * k, d + 2 * k, 0⟩ [fm]⊢* ⟨0, b + 4 * k, c, d, 0⟩ := by
  intro k; induction' k with k ih generalizing b c d
  · exists 0
  · rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (b := b) (c := c + 3) (d := d + 2))
    apply stepStar_trans (drain_round (b := b + 4 * k) (c := c) (d := d))
    ring_nf; finish

theorem end_drain : ⟨0, b, g + 2, 1, 0⟩ [fm]⊢⁺ ⟨0, b + 2, g + 1, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem end_drain0 : ⟨0, b, 1, 1, 0⟩ [fm]⊢⁺ ⟨0, b + 1, 2, 0, 2⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem growth_loop : ∀ k, ⟨0, k, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + 1 + k⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · step fm; step fm; step fm
    rw [show e + 1 + 1 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih (c := c + 2) (e := e + 1))
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring,
        show e + 1 + 1 + k = e + 1 + (k + 1) from by ring]
    finish

theorem trans_ge1 : ⟨0, 0, 3 * f + g + 2, 0, 2 * f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 8 * f + g + 5, 0, 4 * f + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans (e_to_d (2 * f + 1) (c := 3 * f + g + 2) (d := 0))
    rw [show 3 * f + g + 2 = (g + 2) + 3 * f from by ring,
        show 0 + (2 * f + 1) = 1 + 2 * f from by ring]
    exact drain_loop f (b := 0) (c := g + 2) (d := 1)
  · rw [show 0 + 4 * f = 4 * f from by ring]
    apply stepPlus_stepStar_stepPlus (end_drain (b := 4 * f) (g := g))
    rw [show 4 * f + 2 = 4 * f + 2 from rfl]
    apply stepStar_trans (growth_loop (4 * f + 2) (c := g + 1) (e := 0))
    rw [show g + 1 + 2 * (4 * f + 2) = 8 * f + g + 5 from by ring,
        show 0 + 1 + (4 * f + 2) = 4 * f + 3 from by ring]
    finish

theorem trans_eq0 : ⟨0, 0, 3 * f + 1, 0, 2 * f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 8 * f + 4, 0, 4 * f + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
  · apply stepStar_trans (e_to_d (2 * f + 1) (c := 3 * f + 1) (d := 0))
    rw [show 3 * f + 1 = 1 + 3 * f from by ring,
        show 0 + (2 * f + 1) = 1 + 2 * f from by ring]
    exact drain_loop f (b := 0) (c := 1) (d := 1)
  · rw [show 0 + 4 * f = 4 * f from by ring]
    apply stepPlus_stepStar_stepPlus (end_drain0 (b := 4 * f))
    apply stepStar_trans (growth_loop (4 * f + 1) (c := 2) (e := 1))
    rw [show 2 + 2 * (4 * f + 1) = 8 * f + 4 from by ring,
        show 1 + 1 + (4 * f + 1) = 4 * f + 3 from by ring]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨f, g⟩ ↦ ⟨0, 0, 3 * f + 1 + g, 0, 2 * f + 1⟩) ⟨0, 0⟩
  intro ⟨f, g⟩
  rcases g with _ | g
  · exact ⟨⟨2 * f + 1, 2 * f⟩, by show ⟨0, 0, 3 * f + 1, 0, 2 * f + 1⟩ [fm]⊢⁺
      ⟨0, 0, 3 * (2 * f + 1) + 1 + 2 * f, 0, 2 * (2 * f + 1) + 1⟩; rw [show
      3 * (2 * f + 1) + 1 + 2 * f = 8 * f + 4 from by ring, show
      2 * (2 * f + 1) + 1 = 4 * f + 3 from by ring]; exact trans_eq0⟩
  · exact ⟨⟨2 * f + 1, g + 2 * f + 1⟩, by show ⟨0, 0, 3 * f + 1 + (g + 1), 0, 2 * f + 1⟩ [fm]⊢⁺
      ⟨0, 0, 3 * (2 * f + 1) + 1 + (g + 2 * f + 1), 0, 2 * (2 * f + 1) + 1⟩; rw [show
      3 * f + 1 + (g + 1) = 3 * f + g + 2 from by ring, show
      3 * (2 * f + 1) + 1 + (g + 2 * f + 1) = 8 * f + g + 5 from by ring, show
      2 * (2 * f + 1) + 1 = 4 * f + 3 from by ring]; exact trans_ge1⟩
