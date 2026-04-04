import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1937: [9/70, 35/33, 10/3, 11/5, 21/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1  1  1 -1
 1 -1  1  0  0
 0  0 -1  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1937

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r1r2_chain : ∀ k, ⟨a + k, b, 1, 2, e + k⟩ [fm]⊢* ⟨a, b + k, 1, 2, e⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    step fm
    step fm
    rw [show b + k + 1 = b + (k + 1) from by ring]
    finish

theorem r2_chain_0 : ∀ k, ⟨0, b + k, c, d, k⟩ [fm]⊢* ⟨0, b, c + k, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing b c d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b := b) (c := c + 1) (d := d + 1))
    rw [show c + 1 + k = c + (k + 1) from by ring,
        show d + 1 + k = d + (k + 1) from by ring]
    finish

theorem r3r1_chain : ∀ k, ⟨0, b + 1, c + 1, k, 0⟩ [fm]⊢* ⟨0, b + k + 1, c + 1, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b := b + 1))
    rw [show b + 1 + k + 1 = b + (k + 1) + 1 from by ring]
    finish

theorem r3_step : ⟨a, b + 1, c, 0, 0⟩ [fm]⊢ ⟨a + 1, b, c + 1, 0, 0⟩ := by
  simp [fm]

theorem r3_chain : ∀ k, ⟨a, b + k, c, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih (a := a) (b := b + 1))
    exact step_stepStar (r3_step)

theorem c_to_e : ∀ k, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e := e + 1))
    rw [show e + 1 + k = e + (k + 1) from by ring]
    finish

theorem mid_drain : ⟨n + 1, 0, 1, 2, 2 * n + 1⟩ [fm]⊢* ⟨0, 1, n + 1, n + 2, 0⟩ := by
  rw [show (n + 1 : ℕ) = 0 + (n + 1) from by ring,
      show 2 * n + 1 = n + (n + 1) from by ring]
  apply stepStar_trans (r1r2_chain (n + 1) (a := 0) (b := 0) (e := n))
  rw [show (0 + (n + 1) : ℕ) = 1 + n from by ring]
  apply stepStar_trans (r2_chain_0 n (b := 1) (c := 1) (d := 2))
  rw [show 1 + n = n + 1 from by ring, show 2 + n = n + 2 from by ring]
  finish

theorem build_phase : ⟨0, 2, n + 1, n + 1, 0⟩ [fm]⊢* ⟨n + 3, 0, 2 * n + 4, 0, 0⟩ := by
  apply stepStar_trans (r3r1_chain (n + 1) (b := 1) (c := n))
  rw [show 1 + (n + 1) + 1 = n + 3 from by ring,
      show (n + 3 : ℕ) = 0 + (n + 3) from by ring,
      show 2 * n + 4 = (n + 1) + (n + 3) from by ring]
  exact r3_chain (n + 3) (a := 0) (b := 0) (c := n + 1)

theorem main_trans : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
  step fm
  step fm
  show ⟨n + 1, 0, 1, 2, 2 * n + 1⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * n + 4⟩
  apply stepStar_trans mid_drain
  step fm
  step fm
  show ⟨0, 2, n + 1, n + 1, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * n + 4⟩
  apply stepStar_trans build_phase
  have h := c_to_e (2 * n + 4) (a := n + 3) (e := 0)
  rw [show 0 + (2 * n + 4) = 2 * n + 4 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans⟩
