import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1109: [5/6, 4/35, 539/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1109

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b := b + 1)); ring_nf; finish

theorem r3_drain : ∀ A, ⟨A, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * A, e + A⟩ := by
  intro A; induction' A with A ih generalizing d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 2) (e := e + 1)); ring_nf; finish

theorem tail : ∀ k, ⟨A, 0, 2 * k + 1, 2, e⟩ [fm]⊢* ⟨A + 3 * k + 2, 0, 0, 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing A e
  · step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring]
    step fm
    rw [show (2 * k + 2 : ℕ) = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (A := A + 3) (e := e + 1)); ring_nf; finish

theorem spiral_phase : ∀ n c e, ⟨0, 3 * n + 2, c, 0, e + n + 1⟩ [fm]⊢*
    ⟨0, 0, c + 2 * n + 1, 2, e + 1⟩ := by
  intro n; induction' n with n ih
  · intro c e; rw [show e + 0 + 1 = e + 1 from by ring, show c + 2 * 0 + 1 = c + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm; finish
  · intro c e
    rw [show 3 * (n + 1) + 2 = (3 * n + 4) + 1 from by ring,
        show e + (n + 1) + 1 = (e + n + 1) + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (c + 2) e)
    rw [show c + 2 + 2 * n + 1 = c + 2 * (n + 1) + 1 from by ring]; finish

theorem spiral_full : ∀ n e, ⟨0, 3 * n + 2, 0, 0, e + n + 1⟩ [fm]⊢*
    ⟨3 * n + 2, 0, 0, 1, e + n + 1⟩ := by
  intro n e
  apply stepStar_trans (spiral_phase n 0 e)
  rw [show 0 + 2 * n + 1 = 2 * n + 1 from by ring]
  apply stepStar_trans (tail n (A := 0) (e := e + 1))
  ring_nf; finish

theorem main_transition : ∀ n e,
    ⟨0, 0, 0, 3 * n + 2, e + n + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 5, e + 4 * n + 3⟩ := by
  intro n e
  rw [show (3 * n + 2 : ℕ) = (3 * n + 1) + 1 from by ring]
  step fm
  rw [show (3 * n + 1 : ℕ) = 0 + (3 * n + 1) from by ring]
  apply stepStar_trans (d_to_b (3 * n + 1) (b := 1) (d := 0) (e := e + n + 1))
  rw [show 1 + (3 * n + 1) = 3 * n + 2 from by ring]
  apply stepStar_trans (spiral_full n e)
  apply stepStar_trans (r3_drain (3 * n + 2) (d := 1) (e := e + n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨0, 0, 0, 3 * n + 2, e + n + 1⟩)
  · intro c ⟨n, e, hq⟩; subst hq
    exact ⟨⟨0, 0, 0, 6 * n + 5, e + 4 * n + 3⟩,
      ⟨2 * n + 1, e + 2 * n + 1, by ring_nf⟩,
      main_transition n e⟩
  · exact ⟨0, 0, by ring_nf⟩
