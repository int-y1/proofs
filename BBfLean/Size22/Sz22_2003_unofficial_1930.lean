import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1930: [9/70, 25/21, 22/5, 7/11, 25/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1  2 -1  0
 1  0 -1  0  1
 0  0  0  1 -1
-1  0  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1930

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem b_drain : ∀ k, ∀ a b e, ⟨a, b + k, 2, 0, e⟩ [fm]⊢* ⟨a + 2 * k, b, 2, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show a + 1 + 1 = a + 2 from by ring]
    apply stepStar_trans (ih (a + 2) b (e + 1))
    ring_nf; finish

theorem r1r1r2_drain : ∀ k, ⟨a + 2 * k, b, 2, d + 3 * k, 0⟩ [fm]⊢* ⟨a, b + 3 * k, 2, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (a := a + 2) (d := d + 3))
    rw [show a + 2 = a + 1 + 1 from by ring,
        show d + 3 = d + 2 + 1 from by ring]
    step fm
    rw [show d + 2 = d + 1 + 1 from by ring]
    step fm; step fm
    ring_nf; finish

theorem endgame_r2 : ⟨a + 3, b, 2, 2, 0⟩ [fm]⊢⁺ ⟨a, b + 4, 2, 0, 0⟩ := by
  step fm; step fm; step fm; finish

theorem main_trans : ⟨m, 6 * n + 6, 2, 0, 0⟩ [fm]⊢⁺ ⟨m + 16 * n + 19, 6 * n + 12, 2, 0, 0⟩ := by
  -- Step 1: b_drain(6*(n+1))
  rw [show (6 * n + 6 : ℕ) = 0 + (6 * n + 6) from by ring]
  apply stepStar_stepPlus_stepPlus (b_drain (6 * n + 6) (a := m) (b := 0) (e := 0))
  -- now at (m + 2*(6*n+6), 0, 2, 0, 6*n+6) = (m + 12*n + 12, 0, 2, 0, 6*n+6)
  -- R3, R3
  show ⟨m + 2 * (6 * n + 6), 0, 2, 0, 0 + (6 * n + 6)⟩ [fm]⊢⁺ _
  rw [show m + 2 * (6 * n + 6) = m + 12 * n + 12 from by ring,
      show (0 : ℕ) + (6 * n + 6) = 6 * n + 6 from by ring]
  step fm; step fm
  -- now at (m + 12*n + 14, 0, 0, 0, 6*n + 8)
  rw [show m + 12 * n + 12 + 1 + 1 = m + 12 * n + 14 from by ring,
      show 6 * n + 6 + 1 + 1 = 6 * n + 8 from by ring]
  -- e_to_d(6*n+8)
  rw [show (6 * n + 8 : ℕ) = 0 + (6 * n + 8) from by ring]
  apply stepStar_trans (e_to_d (6 * n + 8) (a := m + 12 * n + 14) (d := 0) (e := 0))
  -- now at (m + 12*n + 14, 0, 0, 6*n+8, 0). R5:
  rw [show (0 : ℕ) + (6 * n + 8) = 6 * n + 8 from by ring,
      show m + 12 * n + 14 = (m + 12 * n + 13) + 1 from by ring]
  step fm
  -- now at (m + 12*n + 13, 0, 2, 6*n+8, 0)
  -- r1r1r2_drain(2*n+2): D = 6*n+8 = 2 + 3*(2*n+2)
  rw [show m + 12 * n + 13 = (m + 8 * n + 9) + 2 * (2 * n + 2) from by ring,
      show 6 * n + 8 = 2 + 3 * (2 * n + 2) from by ring]
  apply stepStar_trans (r1r1r2_drain (2 * n + 2) (a := m + 8 * n + 9) (b := 0) (d := 2))
  -- now at (m + 8*n + 9, 6*n+6, 2, 2, 0)
  rw [show (0 : ℕ) + 3 * (2 * n + 2) = 6 * n + 6 from by ring]
  -- endgame_r2
  rw [show m + 8 * n + 9 = (m + 8 * n + 6) + 3 from by ring]
  apply stepStar_trans (stepPlus_stepStar (endgame_r2 (a := m + 8 * n + 6) (b := 6 * n + 6)))
  rw [show 6 * n + 6 + 4 = 6 * n + 10 from by ring]
  -- now at (m + 8*n + 6, 6*n+10, 2, 0, 0)
  -- Step 2: b_drain(6*n+10)
  rw [show (6 * n + 10 : ℕ) = 0 + (6 * n + 10) from by ring]
  apply stepStar_trans (b_drain (6 * n + 10) (a := m + 8 * n + 6) (b := 0) (e := 0))
  rw [show m + 8 * n + 6 + 2 * (6 * n + 10) = m + 20 * n + 26 from by ring,
      show (0 : ℕ) + (6 * n + 10) = 6 * n + 10 from by ring]
  -- R3, R3
  step fm; step fm
  show ⟨m + 20 * n + 26 + 1 + 1, 0, 0, 0, 6 * n + 10 + 1 + 1⟩ [fm]⊢* _
  rw [show m + 20 * n + 26 + 1 + 1 = m + 20 * n + 28 from by ring,
      show 6 * n + 10 + 1 + 1 = 6 * n + 12 from by ring]
  -- e_to_d(6*n+12)
  rw [show (6 * n + 12 : ℕ) = 0 + (6 * n + 12) from by ring]
  apply stepStar_trans (e_to_d (6 * n + 12) (a := m + 20 * n + 28) (d := 0) (e := 0))
  rw [show (0 : ℕ) + (6 * n + 12) = 6 * n + 12 from by ring]
  -- R5
  rw [show m + 20 * n + 28 = (m + 20 * n + 27) + 1 from by ring]
  step fm
  -- r1r1r2_drain(2*n+4): D = 6*n+12 = 0 + 3*(2*n+4)
  show ⟨m + 20 * n + 27, 0, 2, 6 * n + 12, 0⟩ [fm]⊢* _
  rw [show m + 20 * n + 27 = (m + 16 * n + 19) + 2 * (2 * n + 4) from by ring,
      show 6 * n + 12 = 0 + 3 * (2 * n + 4) from by ring]
  apply stepStar_trans (r1r1r2_drain (2 * n + 4) (a := m + 16 * n + 19) (b := 0) (d := 0))
  rw [show (0 : ℕ) + 3 * (2 * n + 4) = 6 * n + 12 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 6, 2, 0, 0⟩) (by execute fm 58)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, n⟩ ↦ ⟨m, 6 * n + 6, 2, 0, 0⟩) ⟨7, 0⟩
  intro ⟨m, n⟩
  exact ⟨⟨m + 16 * n + 19, n + 1⟩, by show ⟨m, 6 * n + 6, 2, 0, 0⟩ [fm]⊢⁺ ⟨m + 16 * n + 19, 6 * (n + 1) + 6, 2, 0, 0⟩; rw [show 6 * (n + 1) + 6 = 6 * n + 12 from by ring]; exact main_trans⟩
