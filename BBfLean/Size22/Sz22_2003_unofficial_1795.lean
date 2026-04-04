import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1795: [9/10, 49/2, 44/21, 25/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  2  0
 2 -1  0 -1  1
 0  0  2  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1795

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_c : ∀ k c d, ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d; step fm
    apply stepStar_trans (ih (c + 2) d)
    ring_nf; finish

theorem spiral : ∀ k b d e, ⟨(0 : ℕ), b + 1, 2 * k, d + k, e⟩ [fm]⊢* ⟨0, b + 3 * k + 1, 0, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show d + (k + 1) = (d + k) + 1 from by omega]
    step fm
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by omega]
    step fm; step fm
    rw [show b + 2 + 2 = (b + 3) + 1 from by omega]
    apply stepStar_trans (ih (b + 3) d (e + 1))
    ring_nf; finish

theorem drain : ∀ k b d e, ⟨(0 : ℕ), b + k, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + 3 * k + 1, e + k⟩ := by
  intro k; induction k with
  | zero => intro b d e; exists 0
  | succ k ih =>
    intro b d e
    rw [show b + (k + 1) = (b + k) + 1 from by omega]
    step fm; step fm; step fm
    rw [show d + 2 + 2 = (d + 3) + 1 from by omega]
    apply stepStar_trans (ih b (d + 3) (e + 1))
    ring_nf; finish

theorem main_trans (d e : ℕ) : ⟨(0 : ℕ), 0, 0, d + 2 * e + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 10 * e + 4, 4 * e + 1⟩ := by
  rcases e with _ | e
  · rw [show d + 2 * 0 + 2 = (d + 1) + 1 from by omega]
    step fm; step fm; step fm; step fm
    rw [show d + 2 + 2 = d + 4 from by omega,
        show d + 10 * 0 + 4 = d + 4 from by omega,
        show 4 * 0 + 1 = 1 from by omega]
    finish
  · apply stepStar_stepPlus_stepPlus (e_to_c (e + 1) 0 (d + 2 * (e + 1) + 2))
    rw [show (0 : ℕ) + 2 * (e + 1) = 2 * (e + 1) from by omega,
        show d + 2 * (e + 1) + 2 = (d + 2 * (e + 1) + 1) + 1 from by omega]
    step fm
    rw [show d + 2 * (e + 1) + 1 = (d + e + 2) + (e + 1) from by omega,
        show (1 : ℕ) = 0 + 1 from by omega]
    apply stepStar_trans (spiral (e + 1) 0 (d + e + 2) 0)
    rw [show (0 : ℕ) + 3 * (e + 1) + 1 = 0 + (3 * e + 4) from by omega,
        show (0 : ℕ) + (e + 1) = e + 1 from by omega,
        show d + e + 2 = (d + e + 1) + 1 from by omega]
    apply stepStar_trans (drain (3 * e + 4) 0 (d + e + 1) (e + 1))
    rw [show d + e + 1 + 3 * (3 * e + 4) + 1 = d + 10 * (e + 1) + 4 from by ring,
        show (e + 1) + (3 * e + 4) = 4 * (e + 1) + 1 from by ring]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 2 * e + 2, e⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  refine ⟨⟨d + 2 * e, 4 * e + 1⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 0, d + 2 * e + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, (d + 2 * e) + 2 * (4 * e + 1) + 2, 4 * e + 1⟩
  rw [show (d + 2 * e) + 2 * (4 * e + 1) + 2 = d + 10 * e + 4 from by ring]
  exact main_trans d e
