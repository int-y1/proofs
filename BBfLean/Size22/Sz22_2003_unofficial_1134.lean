import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1134: [5/6, 44/35, 49/2, 3/11, 5/7, 1/5]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  1  0  0 -1
 0  0  1 -1  0
 0  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1134

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- R3 repeated: drain a into d.
theorem a_to_d : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (d := d + 2))
    ring_nf; finish

-- R4 repeated: move e to b.
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (e := e))
    ring_nf; finish

-- k rounds of R2+R1+R1.
theorem rounds : ∀ k, ⟨0, b + 2 * k, c + 1, D + k, e⟩ [fm]⊢* ⟨0, b, c + k + 1, D, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c D e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show D + (k + 1) = (D + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R2+R1 when b=1.
theorem odd_step : ⟨0, 1, c + 1, D + 1, e⟩ [fm]⊢* ⟨1, 0, c + 1, D, e + 1⟩ := by
  step fm; step fm; finish

-- R2 drain when b=0.
theorem r2_drain : ∀ k, ⟨a, 0, k + 1, D + k + 1, e⟩ [fm]⊢* ⟨a + 2 * k + 2, 0, 0, D, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a D e
  · step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring,
        show D + (k + 1) + 1 = (D + 1) + k + 1 from by ring]
    step fm
    rw [show D + 1 + k = D + k + 1 from by ring]
    apply stepStar_trans (ih (a := a + 2) (D := D) (e := e + 1))
    ring_nf; finish

-- Even case: n=2*k. (2*k+1, 0, 0, d, 2*k) →⁺ (2*k+2, 0, 0, d+2*k, 2*k+1)
theorem trans_even :
    ⟨2 * k + 1, 0, 0, d, 2 * k⟩ [fm]⊢⁺ ⟨2 * k + 2, 0, 0, d + 2 * k, 2 * k + 1⟩ := by
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm
  -- Phase 1: drain a (=2k) into d via R3
  have p1 : ⟨2 * k, 0, 0, d + 2, 2 * k⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * k + 2, 2 * k⟩ := by
    have := a_to_d (2 * k) (a := 0) (d := d + 2) (e := 2 * k)
    simp only [Nat.zero_add] at this
    rw [show d + 2 + 2 * (2 * k) = d + 4 * k + 2 from by ring] at this
    exact this
  apply stepStar_trans p1
  -- Phase 2: move e (=2k) to b via R4
  have p2 : ⟨0, 0, 0, d + 4 * k + 2, 2 * k⟩ [fm]⊢* ⟨0, 2 * k, 0, d + 4 * k + 2, 0⟩ := by
    have := e_to_b (2 * k) (b := 0) (d := d + 4 * k + 2) (e := 0)
    simp only [Nat.zero_add] at this; exact this
  apply stepStar_trans p2
  -- Phase 3: R5 step
  have p3 : ⟨0, 2 * k, 0, d + 4 * k + 2, 0⟩ [fm]⊢* ⟨0, 2 * k, 1, d + 4 * k + 1, 0⟩ := by
    rw [show d + 4 * k + 2 = (d + 4 * k + 1) + 1 from by ring]; step fm; finish
  apply stepStar_trans p3
  -- Phase 4: k rounds of R2+R1+R1
  have p4 : ⟨0, 2 * k, 1, d + 4 * k + 1, 0⟩ [fm]⊢* ⟨0, 0, k + 1, d + 3 * k + 1, k⟩ := by
    have := rounds k (b := 0) (c := 0) (D := d + 3 * k + 1) (e := 0)
    rw [show 0 + 2 * k = 2 * k from by ring,
        show (0 : ℕ) + 1 = 1 from by ring,
        show d + 3 * k + 1 + k = d + 4 * k + 1 from by ring,
        show 0 + k + 1 = k + 1 from by ring,
        show 0 + k = k from by ring] at this
    exact this
  apply stepStar_trans p4
  -- Phase 5: R2 drain
  have p5 : ⟨0, 0, k + 1, d + 3 * k + 1, k⟩ [fm]⊢* ⟨2 * k + 2, 0, 0, d + 2 * k, 2 * k + 1⟩ := by
    have := r2_drain k (a := 0) (D := d + 2 * k) (e := k)
    rw [show d + 2 * k + k + 1 = d + 3 * k + 1 from by ring,
        show 0 + 2 * k + 2 = 2 * k + 2 from by ring,
        show k + k + 1 = 2 * k + 1 from by ring] at this
    exact this
  exact p5

-- Odd case: n=2*k+1. (2*k+2, 0, 0, d, 2*k+1) →⁺ (2*k+3, 0, 0, d+2*k+1, 2*k+2)
theorem trans_odd :
    ⟨2 * k + 2, 0, 0, d, 2 * k + 1⟩ [fm]⊢⁺ ⟨2 * k + 3, 0, 0, d + 2 * k + 1, 2 * k + 2⟩ := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  -- Phase 1: drain a (=2k+1) into d via R3
  have p1 : ⟨2 * k + 1, 0, 0, d + 2, 2 * k + 1⟩ [fm]⊢* ⟨0, 0, 0, d + 4 * k + 4, 2 * k + 1⟩ := by
    have := a_to_d (2 * k + 1) (a := 0) (d := d + 2) (e := 2 * k + 1)
    simp only [Nat.zero_add] at this
    rw [show d + 2 + 2 * (2 * k + 1) = d + 4 * k + 4 from by ring] at this
    exact this
  apply stepStar_trans p1
  -- Phase 2: move e (=2k+1) to b via R4
  have p2 : ⟨0, 0, 0, d + 4 * k + 4, 2 * k + 1⟩ [fm]⊢* ⟨0, 2 * k + 1, 0, d + 4 * k + 4, 0⟩ := by
    have := e_to_b (2 * k + 1) (b := 0) (d := d + 4 * k + 4) (e := 0)
    simp only [Nat.zero_add] at this; exact this
  apply stepStar_trans p2
  -- Phase 3: R5 step
  have p3 : ⟨0, 2 * k + 1, 0, d + 4 * k + 4, 0⟩ [fm]⊢* ⟨0, 2 * k + 1, 1, d + 4 * k + 3, 0⟩ := by
    rw [show d + 4 * k + 4 = (d + 4 * k + 3) + 1 from by ring]; step fm; finish
  apply stepStar_trans p3
  -- Phase 4: k rounds of R2+R1+R1
  have p4 : ⟨0, 2 * k + 1, 1, d + 4 * k + 3, 0⟩ [fm]⊢* ⟨0, 1, k + 1, d + 3 * k + 3, k⟩ := by
    have := rounds k (b := 1) (c := 0) (D := d + 3 * k + 3) (e := 0)
    rw [show 1 + 2 * k = 2 * k + 1 from by ring,
        show (0 : ℕ) + 1 = 1 from by ring,
        show d + 3 * k + 3 + k = d + 4 * k + 3 from by ring,
        show 0 + k + 1 = k + 1 from by ring,
        show 0 + k = k from by ring] at this
    exact this
  apply stepStar_trans p4
  -- Phase 5: odd step (R2+R1 when b=1)
  have p5 : ⟨0, 1, k + 1, d + 3 * k + 3, k⟩ [fm]⊢* ⟨1, 0, k + 1, d + 3 * k + 2, k + 1⟩ := by
    rw [show d + 3 * k + 3 = (d + 3 * k + 2) + 1 from by ring]
    exact odd_step (c := k) (D := d + 3 * k + 2) (e := k)
  apply stepStar_trans p5
  -- Phase 6: R2 drain
  have p6 : ⟨1, 0, k + 1, d + 3 * k + 2, k + 1⟩ [fm]⊢* ⟨2 * k + 3, 0, 0, d + 2 * k + 1, 2 * k + 2⟩ := by
    have := r2_drain k (a := 1) (D := d + 2 * k + 1) (e := k + 1)
    rw [show d + 2 * k + 1 + k + 1 = d + 3 * k + 2 from by ring,
        show 1 + 2 * k + 2 = 2 * k + 3 from by ring,
        show k + 1 + k + 1 = 2 * k + 2 from by ring] at this
    exact this
  exact p6

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, d⟩ ↦ ⟨n + 1, 0, 0, d, n⟩) ⟨0, 0⟩
  intro ⟨n, d⟩
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n even: n = 2*k
    rw [show k + k = 2 * k from by ring] at hk; subst hk
    exact ⟨⟨2 * k + 1, d + 2 * k⟩, trans_even⟩
  · -- n odd: n = 2*k + 1
    subst hk
    exact ⟨⟨2 * k + 2, d + 2 * k + 1⟩, trans_odd⟩

end Sz22_2003_unofficial_1134
