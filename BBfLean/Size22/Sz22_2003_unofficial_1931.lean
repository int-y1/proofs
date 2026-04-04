import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1931: [9/70, 25/33, 22/5, 7/11, 25/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1  2  0 -1
 1  0 -1  0  1
 0  0  0  1 -1
-1  0  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1931

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih (d := d + 1)

theorem c_to_ae : ∀ k, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem drain_round : ⟨a + 3, b, 0, D + 2, 0⟩ [fm]⊢* ⟨a, b + 4, 0, D, 0⟩ := by
  step fm; step fm; step fm; finish

theorem drain_loop : ∀ k, ⟨a + 3 * k, b, 0, 2 * k, 0⟩ [fm]⊢* ⟨a, b + 4 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans drain_round
    apply stepStar_trans (ih (a := a) (b := b + 4))
    ring_nf; finish

theorem r3r2_chain : ∀ k, ⟨a, b + k, c + 1, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + k + 1, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b) (c := c + 1))
    ring_nf; finish

theorem build_phase : ⟨A + 1, 4 * d + 4, 0, 0, 0⟩ [fm]⊢⁺
    ⟨A + 8 * d + 10, 0, 0, 4 * d + 6, 0⟩ := by
  step fm
  step fm
  step fm
  rw [show (4 * d + 3 : ℕ) = 0 + (4 * d + 3) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (4 * d + 3) (a := A + 1) (b := 0) (c := 2))
  rw [show A + 1 + (4 * d + 3) = A + 4 * d + 4 from by ring,
      show 2 + (4 * d + 3) + 1 = 4 * d + 6 from by ring]
  apply stepStar_trans (c_to_ae (4 * d + 6) (a := A + 4 * d + 4) (e := 0))
  rw [show A + 4 * d + 4 + (4 * d + 6) = A + 8 * d + 10 from by ring,
      show 0 + (4 * d + 6) = 4 * d + 6 from by ring]
  apply stepStar_trans (e_to_d (4 * d + 6) (a := A + 8 * d + 10) (d := 0))
  ring_nf; finish

theorem main_trans : ∀ A d, ⟨A + 3 * d + 4, 0, 0, 2 * d + 2, 0⟩ [fm]⊢⁺
    ⟨A + 8 * d + 10, 0, 0, 4 * d + 6, 0⟩ := by
  intro A d
  rw [show A + 3 * d + 4 = (A + 1) + 3 * (d + 1) from by ring,
      show 2 * d + 2 = 2 * (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact drain_loop (d + 1) (a := A + 1) (b := 0)
  rw [show 0 + 4 * (d + 1) = 4 * d + 4 from by ring]
  exact build_phase

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 4, 0⟩) (by execute fm 24)
  show ¬halts fm (⟨0 + 3 * 1 + 4, 0, 0, 2 * 1 + 2, 0⟩ : Q)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, d⟩ ↦ ⟨A + 3 * d + 4, 0, 0, 2 * d + 2, 0⟩) ⟨0, 1⟩
  intro ⟨A, d⟩
  refine ⟨⟨A + 2 * d, 2 * d + 2⟩, ?_⟩
  show ⟨A + 3 * d + 4, 0, 0, 2 * d + 2, 0⟩ [fm]⊢⁺
    ⟨(A + 2 * d) + 3 * (2 * d + 2) + 4, 0, 0, 2 * (2 * d + 2) + 2, 0⟩
  rw [show (A + 2 * d) + 3 * (2 * d + 2) + 4 = A + 8 * d + 10 from by ring,
      show 2 * (2 * d + 2) + 2 = 4 * d + 6 from by ring]
  exact main_trans A d
