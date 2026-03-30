import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #905: [4/15, 3/14, 275/2, 7/25, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0  0 -2  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_905

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [Nat.add_succ a k]; step fm
    apply stepStar_trans (ih (a := a) (c := c + 2) (e := e + 1)); ring_nf; finish

theorem r4_chain : ∀ k, ⟨0, 0, c + 2 * k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [show c + 2 * (k + 1) = c + 2 * k + 1 + 1 from by ring]; step fm
    apply stepStar_trans (ih (c := c) (d := d + 1)); ring_nf; finish

theorem r3_r4_chain : ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, a + 1, e + a + 1⟩ := by
  apply stepStar_trans
  · rw [show a + 1 = 0 + (a + 1) from by ring]
    exact r3_chain (a + 1) (a := 0) (c := 0) (e := e)
  apply stepStar_trans (r4_chain (a + 1) (c := 0) (d := 0) (e := e + (a + 1)))
  ring_nf; finish

theorem even_b_drain : ∀ k, ⟨a + 1, 2 * (k + 1), 0, 0, e⟩ [fm]⊢*
    ⟨a + 3 * (k + 1) + 1, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm; rw [show a + 2 + 2 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 3) (e := e + 1)); ring_nf; finish

theorem odd_b_drain : ∀ k, ⟨a + 1, 2 * k + 3, 0, 0, e⟩ [fm]⊢*
    ⟨a + 3 * (k + 1) + 1, 1, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 1 + 1 from by ring]
    step fm; step fm; step fm; rw [show a + 2 + 2 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 3) (e := e + 1)); ring_nf; finish

theorem staircase_first : ⟨0, 0, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, 2, 0, d, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem staircase_next : ⟨0, 2 * (j + 1), 0, d + 3, e + 1⟩ [fm]⊢*
    ⟨0, 2 * (j + 1) + 2, 0, d, e⟩ := by
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by ring]
  step fm; step fm
  rw [show d + 3 = (d + 2) + 1 from by ring]; step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]; step fm; step fm
  rw [show 2 * j + 1 + 1 + 2 = 2 * (j + 1) + 2 from by ring]; finish

theorem staircase_loop : ∀ k, ⟨0, 2 * (j + 1), 0, 3 * k + r, e + k⟩ [fm]⊢*
    ⟨0, 2 * (j + k + 1), 0, r, e⟩ := by
  intro k; induction' k with k ih generalizing j e
  · ring_nf; finish
  · rw [show 3 * (k + 1) + r = (3 * k + r) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans staircase_next
    rw [show 2 * (j + 1) + 2 = 2 * ((j + 1) + 1) from by ring]
    apply stepStar_trans (ih (j := j + 1) (e := e))
    rw [show j + 1 + k + 1 = j + (k + 1) + 1 from by ring]; finish

theorem full_staircase : ∀ k, ⟨0, 0, 0, 3 * (k + 1) + r, e + k + 1⟩ [fm]⊢*
    ⟨0, 2 * (k + 1), 0, r, e⟩ := by
  intro k
  rw [show 3 * (k + 1) + r = (3 * k + r) + 3 from by ring,
      show e + k + 1 = (e + k) + 1 from by ring]
  apply stepStar_trans staircase_first
  rw [show (2 : ℕ) = 2 * (0 + 1) from by ring]
  apply stepStar_trans (staircase_loop k (j := 0) (r := r) (e := e))
  rw [show 2 * (0 + k + 1) = 2 * (k + 1) from by ring]; finish

theorem r1_tail : ∀ j, ⟨0, 2 * (j + 1), 0, 1, f + 1⟩ [fm]⊢⁺
    ⟨3 * (j + 1) + 2, 0, 0, 0, f + j + 1⟩ := by
  intro j
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show 2 * j + 1 + 1 = 2 * j + 1 + 1 from rfl]
  step fm; step fm
  show ⟨5, 2 * j, 0, 0, f + 1⟩ [fm]⊢* _
  rcases j with _ | j
  · ring_nf; finish
  · rw [show (5 : ℕ) = 4 + 1 from by ring, show 2 * (j + 1) = 2 * (j + 1) from rfl]
    apply stepStar_trans (even_b_drain j (a := 4) (e := f + 1))
    ring_nf; finish

theorem odd_staircase_step : ⟨0, 2 * j + 3, 0, d + 3, e + 1⟩ [fm]⊢*
    ⟨0, 2 * j + 5, 0, d, e⟩ := by
  rw [show 2 * j + 3 = (2 * j + 2) + 1 from by ring]
  step fm; step fm
  rw [show d + 3 = (d + 2) + 1 from by ring]; step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]; step fm; step fm
  rw [show 2 * j + 2 + 1 + 2 = 2 * j + 5 from by ring]; finish

theorem odd_staircase_loop_r : ∀ k, ⟨0, 2 * j + 3, 0, 3 * k + r, e + k⟩ [fm]⊢*
    ⟨0, 2 * (j + k) + 3, 0, r, e⟩ := by
  intro k; induction' k with k ih generalizing j e
  · ring_nf; finish
  · rw [show 3 * (k + 1) + r = (3 * k + r) + 3 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans odd_staircase_step
    rw [show 2 * j + 5 = 2 * (j + 1) + 3 from by ring]
    apply stepStar_trans (ih (j := j + 1) (e := e))
    rw [show j + 1 + k = j + (k + 1) from by ring]; finish

theorem c1_opening : ⟨0, 0, 1, d + 2, f + 1⟩ [fm]⊢* ⟨3, 0, 0, d, f⟩ := by
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; finish

theorem r2_odd_opening : ⟨0, 2 * k + 3, 0, 2, f + 1⟩ [fm]⊢*
    ⟨4, 2 * (k + 1), 0, 0, f + 1⟩ := by
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  rw [show 2 * k + 2 + 1 + 1 = (2 * k + 2 + 1) + 1 from by ring]
  step fm; step fm
  rw [show 2 * k + 2 = 2 * (k + 1) from by ring]; finish

theorem c1d_mod1 : ∀ k, ⟨0, 0, 1, 3 * (k + 1) + 1, g + k + 2⟩ [fm]⊢*
    ⟨3 * (k + 1) + 1, 0, 0, 0, g + k + 2⟩ := by
  intro k; induction' k with k ih generalizing g
  · rw [show 3 * 1 + 1 = 4 from by ring, show g + 0 + 2 = g + 2 from by ring]
    rw [show g + 2 = (g + 1) + 1 from by ring, show (4 : ℕ) = (3 : ℕ) + 1 from by ring]
    step fm; step fm
    rw [show (3 : ℕ) = (2 : ℕ) + 1 from by ring]; step fm; step fm
    rw [show (2 : ℕ) = (1 : ℕ) + 1 from by ring]; step fm; step fm; step fm; step fm
    step fm; step fm
    rw [show (4 : ℕ) = 3 * 1 + 1 from by ring, show g + 2 = g + 0 + 2 from by ring]; finish
  · rw [show 3 * (k + 1 + 1) + 1 = (3 * k + 5) + 2 from by ring,
        show g + (k + 1) + 2 = (g + k + 2) + 1 from by ring]
    apply stepStar_trans c1_opening
    rw [show 3 * k + 5 = (3 * k + 4) + 1 from by ring]; step fm
    rw [show 3 * k + 4 = (3 * k + 3) + 1 from by ring]; step fm
    rw [show 3 * k + 3 = (3 * k + 2) + 1 from by ring]; step fm
    rw [show (3 : ℕ) = 2 * 0 + 3 from by ring, show 3 * k + 2 = 3 * k + 2 from rfl,
        show g + k + 2 = (g + 2) + k from by ring]
    apply stepStar_trans (odd_staircase_loop_r k (j := 0) (r := 2) (e := g + 2))
    rw [show 2 * (0 + k) + 3 = 2 * k + 3 from by ring,
        show g + 2 = (g + 1) + 1 from by ring]
    apply stepStar_trans r2_odd_opening
    rw [show (4 : ℕ) = 3 + 1 from by ring, show g + 1 + 1 = g + 2 from by ring]
    apply stepStar_trans (even_b_drain k (a := 3) (e := g + 2))
    rw [show 3 + 3 * (k + 1) + 1 = 3 * (k + 1 + 1) + 1 from by ring,
        show g + 2 + k + 1 = g + (k + 1) + 2 from by ring]; finish

theorem c1d_mod2 : ∀ k, ⟨0, 0, 1, 3 * (k + 1) + 2, g + k + 2⟩ [fm]⊢*
    ⟨3 * (k + 1) + 3, 0, 0, 0, g + k + 1⟩ := by
  intro k; induction' k with k ih generalizing g
  · rw [show 3 * 1 + 2 = 3 + 2 from by ring, show g + 0 + 2 = (g + 1) + 1 from by ring]
    apply stepStar_trans c1_opening
    rw [show (3 : ℕ) = (2 : ℕ) + 1 from by ring]; step fm; step fm; step fm
    rw [show (3 : ℕ) = (2 : ℕ) + 1 from by ring, show g + 1 = g + 1 from rfl]
    step fm; step fm
    rw [show (3 : ℕ) = 2 + 1 from by ring, show (2 : ℕ) = 2 * 1 from by ring]
    apply stepStar_trans (even_b_drain 0 (a := 2) (e := g))
    rw [show 2 + 3 * 1 + 1 = 3 * 1 + 3 from by ring,
        show g + 0 + 1 = g + 0 + 1 from rfl]; finish
  · rw [show 3 * (k + 1 + 1) + 2 = (3 * k + 6) + 2 from by ring,
        show g + (k + 1) + 2 = (g + k + 2) + 1 from by ring]
    apply stepStar_trans c1_opening
    rw [show 3 * k + 6 = (3 * k + 5) + 1 from by ring]; step fm
    rw [show 3 * k + 5 = (3 * k + 4) + 1 from by ring]; step fm
    rw [show 3 * k + 4 = (3 * k + 3) + 1 from by ring]; step fm
    rw [show (3 : ℕ) = 2 * 0 + 3 from by ring, show 3 * k + 3 = 3 * (k + 1) + 0 from by ring,
        show g + k + 2 = (g + 1) + (k + 1) from by ring]
    apply stepStar_trans (odd_staircase_loop_r (k + 1) (j := 0) (r := 0) (e := g + 1))
    rw [show 2 * (0 + (k + 1)) + 3 = (2 * k + 4) + 1 from by ring]
    step fm; step fm
    rw [show (3 : ℕ) = 2 + 1 from by ring, show 2 * k + 4 = 2 * (k + 1 + 1) from by ring]
    apply stepStar_trans (even_b_drain (k + 1) (a := 2) (e := g))
    rw [show 2 + 3 * (k + 1 + 1) + 1 = 3 * (k + 1 + 1) + 3 from by ring,
        show g + (k + 1) + 1 = g + (k + 1) + 1 from rfl]; finish

theorem drain_r1 : ∀ k, ⟨0, 0, 0, 3 * (k + 1) + 1, g + k + 2⟩ [fm]⊢⁺
    ⟨3 * (k + 1) + 2, 0, 0, 0, g + k + 1⟩ := by
  intro k
  rw [show g + k + 2 = (g + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (full_staircase k (r := 1) (e := g + 1))
  apply stepPlus_stepStar_stepPlus (r1_tail k (f := g)); finish

theorem r2_tail : ∀ j, ⟨0, 2 * (j + 1), 0, 2, f + 1⟩ [fm]⊢⁺
    ⟨3 * (j + 1) + 3, 0, 0, 0, f + 4 * (j + 1) + 2⟩ := by
  intro j
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  rw [show 2 * j + 1 + 1 + 1 = (2 * j + 1 + 1) + 1 from by ring]; step fm
  rw [show 2 * j + 1 + 1 = (2 * j + 1) + 1 from by ring]; step fm
  show ⟨4, 2 * j + 1, 0, 0, f + 1⟩ [fm]⊢* _
  rcases j with _ | j
  · step fm; step fm
    show ⟨5, 0, 1, 0, f + 2⟩ [fm]⊢* _
    rw [show (5 : ℕ) = 0 + 5 from by ring]
    apply stepStar_trans (r3_chain 5 (a := 0) (c := 1) (e := f + 2))
    rw [show 1 + 2 * 5 = 1 + 2 * 5 from rfl, show f + 2 + 5 = f + 7 from by ring]
    apply stepStar_trans (r4_chain 5 (c := 1) (d := 0) (e := f + 7))
    rw [show 0 + 5 = 3 * 1 + 2 from by ring,
        show f + 7 = (f + 5) + 0 + 2 from by ring]
    apply stepStar_trans (c1d_mod2 0 (g := f + 5))
    rw [show 3 * 1 + 3 = 3 * 1 + 3 from rfl,
        show f + 5 + 0 + 1 = f + 4 * 1 + 2 from by ring]; finish
  · rw [show 2 * (j + 1) + 1 = 2 * j + 3 from by ring, show (4 : ℕ) = 3 + 1 from by ring]
    apply stepStar_trans (odd_b_drain j (a := 3) (e := f + 1))
    rw [show 3 + 3 * (j + 1) + 1 = (3 * j + 6) + 1 from by ring,
        show f + 1 + j + 1 = f + j + 2 from by ring]
    step fm; step fm
    show ⟨3 * j + 6 + 2, 0, 1, 0, f + j + 3⟩ [fm]⊢* _
    rw [show 3 * j + 6 + 2 = 0 + (3 * j + 8) from by ring]
    apply stepStar_trans (r3_chain (3 * j + 8) (a := 0) (c := 1) (e := f + j + 3))
    rw [show 1 + 2 * (3 * j + 8) = 1 + 2 * (3 * j + 8) from rfl,
        show f + j + 3 + (3 * j + 8) = f + 4 * j + 11 from by ring]
    apply stepStar_trans (r4_chain (3 * j + 8) (c := 1) (d := 0) (e := f + 4 * j + 11))
    rw [show 0 + (3 * j + 8) = 3 * (j + 1 + 1) + 2 from by ring,
        show f + 4 * j + 11 = (f + 3 * j + 8) + (j + 1) + 2 from by ring]
    apply stepStar_trans (c1d_mod2 (j + 1) (g := f + 3 * j + 8))
    rw [show 3 * (j + 1 + 1) + 3 = 3 * (j + 1 + 1) + 3 from rfl,
        show f + 3 * j + 8 + (j + 1) + 1 = f + 4 * (j + 1 + 1) + 2 from by ring]; finish

theorem drain_r2 : ∀ k, ⟨0, 0, 0, 3 * (k + 1) + 2, g + k + 2⟩ [fm]⊢⁺
    ⟨3 * (k + 1) + 3, 0, 0, 0, g + 4 * (k + 1) + 2⟩ := by
  intro k
  rw [show g + k + 2 = (g + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (full_staircase k (r := 2) (e := g + 1))
  apply stepPlus_stepStar_stepPlus (r2_tail k (f := g)); finish

theorem r0_tail : ∀ j, ⟨0, 2 * (j + 1), 0, 0, f + 1⟩ [fm]⊢⁺
    ⟨3 * (j + 1) + 1, 0, 0, 0, f + 4 * (j + 1) + 1⟩ := by
  intro j
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by ring]
  step fm; step fm
  show ⟨3, 2 * j + 1, 0, 0, f⟩ [fm]⊢* _
  rcases j with _ | j
  · step fm; step fm
    show ⟨4, 0, 1, 0, f + 1⟩ [fm]⊢* _
    rw [show (4 : ℕ) = 0 + 4 from by ring]
    apply stepStar_trans (r3_chain 4 (a := 0) (c := 1) (e := f + 1))
    rw [show 1 + 2 * 4 = 1 + 2 * 4 from rfl, show f + 1 + 4 = f + 5 from by ring]
    apply stepStar_trans (r4_chain 4 (c := 1) (d := 0) (e := f + 5))
    rw [show 0 + 4 = 3 * 1 + 1 from by ring,
        show f + 5 = (f + 3) + 0 + 2 from by ring]
    apply stepStar_trans (c1d_mod1 0 (g := f + 3))
    rw [show 3 * 1 + 1 = 3 * 1 + 1 from rfl,
        show f + 3 + 0 + 2 = f + 4 * 1 + 1 from by ring]; finish
  · rw [show 2 * (j + 1) + 1 = 2 * j + 3 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
    apply stepStar_trans (odd_b_drain j (a := 2) (e := f))
    rw [show 2 + 3 * (j + 1) + 1 = (3 * j + 5) + 1 from by ring,
        show f + j + 1 = f + j + 1 from rfl]
    step fm; step fm
    show ⟨3 * j + 5 + 2, 0, 1, 0, f + j + 2⟩ [fm]⊢* _
    rw [show 3 * j + 5 + 2 = 0 + (3 * j + 7) from by ring]
    apply stepStar_trans (r3_chain (3 * j + 7) (a := 0) (c := 1) (e := f + j + 2))
    rw [show 1 + 2 * (3 * j + 7) = 1 + 2 * (3 * j + 7) from rfl,
        show f + j + 2 + (3 * j + 7) = f + 4 * j + 9 from by ring]
    apply stepStar_trans (r4_chain (3 * j + 7) (c := 1) (d := 0) (e := f + 4 * j + 9))
    rw [show 0 + (3 * j + 7) = 3 * (j + 1 + 1) + 1 from by ring,
        show f + 4 * j + 9 = (f + 3 * j + 6) + (j + 1) + 2 from by ring]
    apply stepStar_trans (c1d_mod1 (j + 1) (g := f + 3 * j + 6))
    rw [show 3 * (j + 1 + 1) + 1 = 3 * (j + 1 + 1) + 1 from rfl,
        show f + 3 * j + 6 + (j + 1) + 2 = f + 4 * (j + 1 + 1) + 1 from by ring]; finish

theorem drain_r0 : ∀ k, ⟨0, 0, 0, 3 * (k + 1), g + k + 2⟩ [fm]⊢⁺
    ⟨3 * (k + 1) + 1, 0, 0, 0, g + 4 * (k + 1) + 1⟩ := by
  intro k
  rw [show g + k + 2 = (g + 1) + (k + 1) from by ring,
      show 3 * (k + 1) = 3 * (k + 1) + 0 from by ring]
  apply stepStar_stepPlus_stepPlus (full_staircase k (r := 0) (e := g + 1))
  apply stepPlus_stepStar_stepPlus (r0_tail k (f := g)); finish

theorem case1 : ∀ m e, ⟨3 * m + 1, 0, 0, 0, e⟩ [fm]⊢⁺
    ⟨3 * m + 2, 0, 0, 0, e + 3 * m⟩ := by
  intro m; rcases m with _ | m <;> intro e
  · step fm; step fm; step fm; step fm; step fm; finish
  · apply stepStar_stepPlus_stepPlus
    · apply stepStar_trans (r3_r4_chain (a := 3 * (m + 1)) (e := e))
      rw [show e + (3 * (m + 1)) + 1 = (e + 2 * m + 3) + m + 1 from by ring,
          show 3 * (m + 1) + 1 = 3 * (m + 1) + 1 from rfl]
      exact full_staircase m (r := 1) (e := e + 2 * m + 3)
    rw [show e + 2 * m + 3 = (e + 2 * m + 2) + 1 from by ring]
    apply stepPlus_stepStar_stepPlus (r1_tail m (f := e + 2 * m + 2))
    rw [show e + 2 * m + 2 + m + 1 = e + 3 * (m + 1) from by ring]; finish

theorem case2 : ∀ m e, ⟨3 * m + 2, 0, 0, 0, e⟩ [fm]⊢⁺
    ⟨3 * m + 3, 0, 0, 0, e + 6 * m + 3⟩ := by
  intro m; rcases m with _ | m <;> intro e
  · execute fm 19
  · apply stepStar_stepPlus_stepPlus (r3_r4_chain (a := 3 * (m + 1) + 1) (e := e))
    rw [show e + (3 * (m + 1) + 1) + 1 = (e + 2 * m + 3) + m + 2 from by ring,
        show 3 * (m + 1) + 1 + 1 = 3 * (m + 1) + 2 from by ring]
    apply stepPlus_stepStar_stepPlus (drain_r2 m (g := e + 2 * m + 3))
    rw [show e + 2 * m + 3 + 4 * (m + 1) + 2 = e + 6 * (m + 1) + 3 from by ring,
        show 3 * (m + 1) + 3 = 3 * (m + 1) + 3 from rfl]; finish

theorem case3 : ∀ m e, ⟨3 * m + 3, 0, 0, 0, e⟩ [fm]⊢⁺
    ⟨3 * m + 4, 0, 0, 0, e + 6 * m + 6⟩ := by
  intro m e
  apply stepStar_stepPlus_stepPlus (r3_r4_chain (a := 3 * m + 2) (e := e))
  rw [show e + (3 * m + 2) + 1 = (e + 2 * m + 1) + m + 2 from by ring,
      show 3 * m + 2 + 1 = 3 * (m + 1) from by ring]
  apply stepPlus_stepStar_stepPlus (drain_r0 m (g := e + 2 * m + 1))
  rw [show 3 * (m + 1) + 1 = 3 * m + 4 from by ring,
      show e + 2 * m + 1 + 4 * (m + 1) + 1 = e + 6 * m + 6 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 2, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    obtain ⟨m, hm⟩ : ∃ m, a = 3 * m ∨ a = 3 * m + 1 ∨ a = 3 * m + 2 := by
      exact ⟨a / 3, by omega⟩
    rcases hm with rfl | rfl | rfl
    · -- a = 3*m: (3*m+2, 0, 0, 0, e) → case2
      exact ⟨⟨3 * m + 3, 0, 0, 0, e + 6 * m + 3⟩,
        ⟨3 * m + 1, e + 6 * m + 3, by ring_nf⟩, case2 m e⟩
    · -- a = 3*m+1: (3*m+3, 0, 0, 0, e) → case3
      exact ⟨⟨3 * m + 4, 0, 0, 0, e + 6 * m + 6⟩,
        ⟨3 * m + 2, e + 6 * m + 6, by ring_nf⟩, case3 m e⟩
    · -- a = 3*m+2: (3*m+4, 0, 0, 0, e) → case1(m+1)
      refine ⟨⟨3 * m + 5, 0, 0, 0, e + 3 * m + 3⟩,
        ⟨3 * m + 3, e + 3 * m + 3, by ring_nf⟩, ?_⟩
      rw [show 3 * m + 2 + 2 = 3 * (m + 1) + 1 from by ring,
          show 3 * m + 2 + 3 = 3 * (m + 1) + 2 from by ring,
          show e + 3 * m + 3 = e + 3 * (m + 1) from by ring]
      exact case1 (m + 1) e
  · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_905
