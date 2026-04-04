import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1798: [9/10, 5/21, 539/5, 4/77, 5/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  0
 0  0 -1  2  1
 2  0  0 -1 -1
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1798

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r5r1_chain : ∀ k, ⟨2 * k + 1, b, 0, 0, 0⟩ [fm]⊢* ⟨0, b + 2 * k, 1, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing b
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

theorem opening_succ : ⟨2 * n + 4, 0, 0, 1, 0⟩ [fm]⊢* ⟨0, 2 * n + 3, 1, 0, 0⟩ := by
  rw [show 2 * n + 4 = (2 * n + 1) + 1 + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (r5r1_chain n (b := 3))
  ring_nf; finish

theorem opening : ∀ n, ⟨2 * n + 2, 0, 0, 1, 0⟩ [fm]⊢* ⟨0, 2 * n + 1, 1, 0, 0⟩ := by
  intro n; rcases n with _ | n
  · execute fm 3
  · exact opening_succ

theorem three_step : ⟨0, b + 2, c + 1, 0, e⟩ [fm]⊢* ⟨0, b, c + 2, 0, e + 1⟩ := by
  step fm; step fm; step fm; finish

theorem drain_even : ∀ k, ⟨0, 2 * k + b, c + 1, 0, e⟩ [fm]⊢* ⟨0, b, c + k + 1, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · ring_nf; finish
  · rw [show 2 * (k + 1) + b = (2 * k + b) + 2 from by ring]
    apply stepStar_trans (three_step (b := 2 * k + b) (c := c) (e := e))
    apply stepStar_trans (ih (b := b) (c := c + 1) (e := e + 1))
    ring_nf; finish

theorem tail_drain : ⟨0, 1, c + 1, 0, e⟩ [fm]⊢* ⟨0, 0, c + 1, 1, e + 1⟩ := by
  step fm; step fm; finish

theorem r3_chain : ∀ k, ⟨0, 0, k, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · ring_nf; finish
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (d := d + 2) (e := e + 1))
    ring_nf; finish

theorem r4_step : ⟨a, 0, 0, d + 1, e + 1⟩ [fm]⊢ ⟨a + 2, 0, 0, d, e⟩ := by
  simp [fm]

theorem r4_chain : ∀ k, ⟨a, 0, 0, d + k, k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r4_step (a := a) (d := d + k) (e := k)))
    apply stepStar_trans (ih (a := a + 2) (d := d))
    ring_nf; finish

theorem middle_phase_succ : ⟨0, 2 * n + 3, 1, 0, 0⟩ [fm]⊢* ⟨0, 0, 0, 2 * n + 5, 2 * n + 4⟩ := by
  rw [show 2 * n + 3 = (2 * n + 1) + 1 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (drain_even n (b := 1) (c := 1) (e := 1))
  rw [show 1 + n + 1 = (n + 1) + 1 from by ring,
      show 1 + n = n + 1 from by ring]
  apply stepStar_trans (tail_drain (c := n + 1) (e := n + 1))
  rw [show n + 1 + 1 = n + 2 from by ring,
      show n + 1 + 1 = n + 2 from by ring]
  apply stepStar_trans (r3_chain (n + 2) (d := 1) (e := n + 2))
  ring_nf; finish

theorem middle_phase : ∀ n, ⟨0, 2 * n + 1, 1, 0, 0⟩ [fm]⊢* ⟨0, 0, 0, 2 * n + 3, 2 * n + 2⟩ := by
  intro n; rcases n with _ | n
  · execute fm 3
  · exact middle_phase_succ

theorem opening_plus : ∀ n, ⟨2 * n + 2, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨0, 2 * n + 1, 1, 0, 0⟩ := by
  intro n; rcases n with _ | n
  · execute fm 3
  · rw [show 2 * (n + 1) + 2 = (2 * n + 1) + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (r5r1_chain n (b := 3))
    ring_nf; finish

theorem main_trans : ⟨2 * n + 2, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨4 * n + 4, 0, 0, 1, 0⟩ := by
  apply stepPlus_stepStar_stepPlus (opening_plus n)
  apply stepStar_trans (middle_phase n)
  rw [show 2 * n + 3 = 1 + (2 * n + 2) from by ring]
  apply stepStar_trans (r4_chain (2 * n + 2) (a := 0) (d := 1))
  rw [show 0 + 2 * (2 * n + 2) = 4 * n + 4 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * (n + 1), 0, 0, 1, 0⟩) 0
  intro n
  refine ⟨2 * n + 1, ?_⟩
  show ⟨2 * (n + 1), 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨2 * (2 * n + 1 + 1), 0, 0, 1, 0⟩
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
      show 2 * (2 * n + 1 + 1) = 4 * n + 4 from by ring]
  exact main_trans
