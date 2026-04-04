import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1916: [9/385, 7/15, 50/7, 11/2, 21/11]

Vector representation:
```
 0  2 -1 -1 -1
 0 -1 -1  1  0
 1  0  2 -1  0
-1  0  0  0  1
 0  1  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1916

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a := a + 1) (c := c + 2)); ring_nf; finish

theorem r4_chain : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (a := a) (e := e + 1)); ring_nf; finish

theorem b_drain_step : ⟨m, b + 2, 0, d + 1, 0⟩ [fm]⊢* ⟨m + 1, b, 0, d + 2, 0⟩ := by
  step fm; step fm; step fm; finish

theorem b_drain_even : ∀ k, ∀ m d, ⟨m, 2 * k, 0, d + 1, 0⟩ [fm]⊢*
    ⟨m + k, 0, 0, d + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro m d
  · ring_nf; finish
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans (b_drain_step (m := m) (b := 2 * k) (d := d))
    apply stepStar_trans (ih (m + 1) (d + 1)); ring_nf; finish

theorem b_drain_odd : ∀ k, ∀ m d, ⟨m, 2 * k + 1, 0, d + 1, 0⟩ [fm]⊢*
    ⟨m + k, 1, 0, d + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro m d
  · ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    apply stepStar_trans (b_drain_step (m := m) (b := 2 * k + 1) (d := d))
    apply stepStar_trans (ih (m + 1) (d + 1)); ring_nf; finish

theorem r1r2_pair : ⟨0, b + 1, c + 2, 1, e + 1⟩ [fm]⊢* ⟨0, b + 2, c, 1, e⟩ := by
  step fm; step fm; finish

theorem spiral_core : ∀ d, ∀ b e, ⟨0, b + 1, c + 2 * d, 1, d + e⟩ [fm]⊢*
    ⟨0, b + d + 1, c, 1, e⟩ := by
  intro d; induction' d with d ih <;> intro b e
  · ring_nf; finish
  · rw [show c + 2 * (d + 1) = (c + 2 * d) + 2 from by ring,
        show (d + 1) + e = d + (e + 1) from by ring,
        show b + (d + 1) + 1 = (b + 1) + d + 1 from by ring]
    apply stepStar_trans (r1r2_pair (b := b) (c := c + 2 * d) (e := d + e))
    rw [show b + 2 = (b + 1) + 1 from by ring]
    exact ih (b + 1) e

theorem even_spiral : ⟨0, 0, 2 * (d + 1), 0, d + 1 + (a + 2)⟩ [fm]⊢*
    ⟨0, d + 2, 0, 1, a + 1⟩ := by
  rw [show 2 * (d + 1) = 0 + 2 * d + 1 + 1 from by ring,
      show d + 1 + (a + 2) = (d + a + 2) + 1 from by ring]
  step fm
  rw [show d + a + 2 = (d + a + 1) + 1 from by ring,
      show 0 + 2 * d + 1 + 1 = (0 + 2 * d) + 1 + 1 from by ring]
  step fm
  rw [show d + a + 1 = d + (a + 1) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (spiral_core d 1 (a + 1) (c := 0))
  ring_nf; finish

theorem tail_round : ⟨0, b + 1, 0, 1, e + 2⟩ [fm]⊢* ⟨0, b + 3, 0, 1, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem tail_loop : ∀ e, ∀ b, ⟨0, b + 1, 0, 1, e + 1⟩ [fm]⊢*
    ⟨1, b + 2 * e + 2, 0, 0, 0⟩ := by
  intro e; induction' e with e ih <;> intro b
  · step fm; step fm; step fm; finish
  · rw [show (e + 1) + 1 = e + 2 from by ring]
    apply stepStar_trans (tail_round (b := b) (e := e))
    apply stepStar_trans (ih (b + 2)); ring_nf; finish

theorem main_trans : ⟨a + 2, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨1, d + 2 * a + 3, 0, 0, 0⟩ := by
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain (d + 1) (a := a + 2) (c := 0) (d := 0))
  rw [show 0 + 2 * (d + 1) = 2 * (d + 1) from by ring,
      show a + 2 + (d + 1) = 0 + (a + d + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (a + d + 3) (a := 0) (c := 2 * (d + 1)) (e := 0))
  rw [show 0 + (a + d + 3) = d + 1 + (a + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (even_spiral (d := d) (a := a))
  rw [show d + 2 = (d + 1) + 1 from by ring,
      show d + 2 * a + 3 = (d + 1) + 2 * a + 2 from by ring]
  exact stepStar_stepPlus (tail_loop a (d + 1)) (by intro h; cases h)

theorem odd_B_star : ⟨1, 2 * k + 3, 0, 0, 0⟩ [fm]⊢* ⟨k + 2, 0, 0, k + 3, 0⟩ := by
  step fm; step fm
  rw [show 2 * k + 3 + 1 = 2 * (k + 2) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (b_drain_even (k + 2) 0 0)
  ring_nf; finish

theorem odd_B : ⟨1, 2 * k + 3, 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 3 * k + 5, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus odd_B_star
  rw [show k + 3 = (k + 2) + 1 from by ring,
      show 3 * k + 5 = (k + 2) + 2 * k + 3 from by ring]
  exact main_trans (a := k) (d := k + 2)

theorem odd_c_spiral : ⟨0, 0, 2 * d + 3, 0, d + (m + 5)⟩ [fm]⊢*
    ⟨1, d + 2 * m + 6, 0, 0, 0⟩ := by
  rw [show d + (m + 5) = (d + m + 4) + 1 from by ring]
  step fm  -- R5
  rw [show 2 * d + 3 = 3 + 2 * d from by ring,
      show d + m + 4 = d + (m + 4) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (spiral_core d 0 (m + 4) (c := 3))
  rw [show 0 + d + 1 = d + 1 from by ring,
      show (3 : ℕ) = 1 + 2 from by ring,
      show m + 4 = (m + 3) + 1 from by ring,
      show d + 1 = d + 1 from rfl]
  apply stepStar_trans (r1r2_pair (b := d) (c := 1) (e := m + 3))
  rw [show d + 2 = d + 2 from rfl,
      show (1 : ℕ) = 0 + 1 from by ring,
      show m + 3 = (m + 2) + 1 from by ring]
  step fm  -- R1
  rw [show m + 2 = (m + 1) + 1 from by ring]
  step fm  -- R5
  rw [show d + 2 + 2 + 1 = (d + 4) + 1 from by ring,
      show m + 1 = m + 1 from rfl,
      show d + 2 * m + 6 = (d + 4) + 2 * m + 2 from by ring]
  exact tail_loop m (d + 4)

theorem m1_star : ⟨m + 3, 1, 0, d + 1, 0⟩ [fm]⊢* ⟨0, 0, 2 * d + 3, 0, d + (m + 5)⟩ := by
  step fm; step fm
  rw [show d + 1 = 0 + (d + 1) from by ring,
      show m + 3 + 1 = (m + 4) from by ring]
  apply stepStar_trans (r3_chain (d + 1) (a := m + 4) (c := 1) (d := 0))
  rw [show 1 + 2 * (d + 1) = 2 * d + 3 from by ring,
      show m + 4 + (d + 1) = 0 + (m + d + 5) from by ring]
  apply stepStar_trans (r4_chain (m + d + 5) (a := 0) (c := 2 * d + 3) (e := 0))
  ring_nf; finish

theorem m1_trans : ⟨m + 3, 1, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨1, d + 2 * m + 6, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus m1_star
  rw [show d + 2 * m + 6 = d + 2 * m + 6 from rfl]
  exact stepStar_stepPlus (odd_c_spiral (d := d) (m := m)) (by intro h; cases h)

theorem even_B_star : ⟨1, 2 * (k + 3), 0, 0, 0⟩ [fm]⊢* ⟨k + 3, 1, 0, k + 4, 0⟩ := by
  step fm; step fm
  rw [show 2 * (k + 3) + 1 = 2 * (k + 3) + 1 from rfl,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (b_drain_odd (k + 3) 0 0)
  ring_nf; finish

theorem even_B : ⟨1, 2 * (k + 3), 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 3 * (k + 3), 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus even_B_star
  rw [show k + 4 = (k + 3) + 1 from by ring,
      show 3 * (k + 3) = (k + 3) + 2 * k + 6 from by ring,
      show k + 3 = k + 3 from rfl]
  exact m1_trans (m := k) (d := k + 3)

theorem b4_special : ⟨1, 4, 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 9, 0, 0, 0⟩ := by
  execute fm 65

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 5, 0, 0, 0⟩) (by execute fm 65)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨1, n + 3, 0, 0, 0⟩)
  · intro c ⟨n, hq⟩; subst hq
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      exact ⟨⟨1, 3 * k + 5, 0, 0, 0⟩,
        ⟨3 * k + 2, show (1, 3 * k + 5, 0, 0, 0) = (1, 3 * k + 2 + 3, 0, 0, 0) from by ring_nf⟩,
        by rw [show k + k + 3 = 2 * k + 3 from by ring]; exact odd_B⟩
    · subst hk
      rcases k with _ | _ | k
      · exact ⟨⟨1, 9, 0, 0, 0⟩, ⟨6, rfl⟩, b4_special⟩
      · refine ⟨⟨1, 9, 0, 0, 0⟩, ⟨6, rfl⟩, ?_⟩
        show ⟨1, 2 * (0 + 3), 0, 0, 0⟩ [fm]⊢⁺ _
        apply stepPlus_stepStar_stepPlus (even_B (k := 0))
        ring_nf; finish
      · exact ⟨⟨1, 3 * (k + 4), 0, 0, 0⟩,
          ⟨3 * k + 9, show (1, 3 * (k + 4), 0, 0, 0) = (1, 3 * k + 9 + 3, 0, 0, 0) from by ring_nf⟩,
          by rw [show 2 * (k + 1 + 1) + 1 + 3 = 2 * ((k + 1) + 3) from by ring]
             exact even_B (k := k + 1)⟩
  · exact ⟨2, rfl⟩
