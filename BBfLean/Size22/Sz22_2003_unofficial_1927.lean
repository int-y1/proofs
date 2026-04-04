import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1927: [9/70, 22/5, 25/33, 7/11, 33/2]

Vector representation:
```
-1  2 -1 -1  0
 1  0 -1  0  1
 0 -1  2  0 -1
 0  0  0  1 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1927

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e))
    ring_nf; finish

theorem drain_round : ⟨a + 3, b, 0, d + 2, 0⟩ [fm]⊢* ⟨a, b + 4, 0, d, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem drain : ∀ k, ⟨a + 3 * (k + 1), b, 0, 2 * (k + 1), 0⟩ [fm]⊢* ⟨a, b + 4 * (k + 1), 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · rw [show a + 3 * (0 + 1) = a + 3 from by ring,
        show 2 * (0 + 1) = 0 + 2 from by ring,
        show b + 4 * (0 + 1) = b + 4 from by ring]
    exact drain_round
  · rw [show a + 3 * (k + 1 + 1) = a + 3 * (k + 1) + 3 from by ring,
        show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 from by ring]
    apply stepStar_trans (drain_round (a := a + 3 * (k + 1)) (b := b) (d := 2 * (k + 1)))
    apply stepStar_trans (ih (a := a) (b := b + 4))
    rw [show b + 4 + 4 * (k + 1) = b + 4 * (k + 1 + 1) from by ring]
    finish

theorem expand_start : ⟨a + 1, b, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, b, 0, 0, 2⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem r3r2r2_chain : ∀ k, ⟨a, b + k, 0, 0, e + 1⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a := a + 2) (b := b) (e := e + 1))
    ring_nf; finish

theorem expand : ⟨a + 1, b + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * b + 4, 0, 0, 0, b + 3⟩ := by
  apply stepPlus_stepStar_stepPlus (expand_start (a := a) (b := b + 1))
  rw [show a + 2 = a + 2 from rfl]
  have h := r3r2r2_chain (b + 1) (a := a + 2) (b := 0) (e := 1)
  rw [show (0 : ℕ) + (b + 1) = b + 1 from by ring,
      show (1 : ℕ) + 1 = 2 from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

theorem main_trans : ⟨m + 3 * k + 4, 0, 0, 0, 2 * k + 2⟩ [fm]⊢⁺ ⟨m + 2 * k + 3 * (2 * k + 2) + 4, 0, 0, 0, 2 * (2 * k + 2) + 2⟩ := by
  have phase1 : ⟨m + 3 * k + 4, 0, 0, 0, 2 * k + 2⟩ [fm]⊢* ⟨m + 1, 4 * k + 4, 0, 0, 0⟩ := by
    rw [show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
    apply stepStar_trans (e_to_d (2 * k + 2) (a := m + 3 * k + 4) (d := 0) (e := 0))
    rw [show m + 3 * k + 4 = (m + 1) + 3 * (k + 1) from by ring,
        show 0 + (2 * k + 2) = 2 * (k + 1) from by ring]
    apply stepStar_trans (drain k (a := m + 1) (b := 0))
    rw [show 0 + 4 * (k + 1) = 4 * k + 4 from by ring]
    finish
  have phase2 : ⟨m + 1, 4 * k + 4, 0, 0, 0⟩ [fm]⊢⁺ ⟨m + 2 * k + 3 * (2 * k + 2) + 4, 0, 0, 0, 2 * (2 * k + 2) + 2⟩ := by
    rw [show (m + 1 : ℕ) = m + 1 from rfl,
        show (4 * k + 4 : ℕ) = (4 * k + 3) + 1 from by ring]
    apply stepPlus_stepStar_stepPlus (expand (a := m) (b := 4 * k + 3))
    rw [show m + 2 * (4 * k + 3) + 4 = m + 2 * k + 3 * (2 * k + 2) + 4 from by ring,
        show 4 * k + 3 + 3 = 2 * (2 * k + 2) + 2 from by ring]
    finish
  exact stepStar_stepPlus_stepPlus phase1 phase2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 4⟩) (by execute fm 22)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, k⟩ ↦ ⟨m + 3 * k + 4, 0, 0, 0, 2 * k + 2⟩) ⟨0, 1⟩
  intro ⟨m, k⟩
  exact ⟨⟨m + 2 * k, 2 * k + 2⟩, main_trans⟩
