import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #270: [14/15, 18/7, 1/6, 125/2, 6/5]

Vector representation:
```
 1 -1 -1  1
 1  2  0 -1
-1 -1  0  0
-1  0  3  0
 1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_270

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b+1, c, d⟩
  | _ => none

-- Rule 4 repeated: (a+k, 0, c, 0) →* (a, 0, c+3*k, 0)
theorem a_to_c : ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+3*k, 0⟩ := by
  induction k generalizing a c with
  | zero => exists 0
  | succ k ih =>
    rw [show a + (k + 1) = (a + k) + 1 from by omega]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 3))
    rw [show c + 3 + 3 * k = c + 3 * (k + 1) from by ring]
    finish

-- Rule 3 repeated: (a+k, k, 0, 0) →* (a, 0, 0, 0)
theorem ab_drain : ⟨a+k, k, 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  induction k generalizing a with
  | zero => exists 0
  | succ k ih =>
    rw [show a + (k + 1) = (a + k) + 1 from by omega]
    step fm
    exact ih

-- Rule 2 repeated: (a, b, 0, d) →* (a+d, b+2*d, 0, 0)
theorem d_expand : ⟨a, b, 0, d⟩ [fm]⊢* ⟨a+d, b+2*d, 0, 0⟩ := by
  induction d generalizing a b with
  | zero => exists 0
  | succ d ih =>
    step fm
    apply stepStar_trans (ih (a := a + 1) (b := b + 2))
    rw [show a + 1 + d = a + (d + 1) from by omega,
        show b + 2 + 2 * d = b + 2 * (d + 1) from by ring]
    finish

-- 3-step inner loop: (a, 0, c+2, d+1) →* (a+3, 0, c, d+2)
theorem inner_step : ⟨a, 0, c+2, d+1⟩ [fm]⊢* ⟨a+3, 0, c, d+2⟩ := by
  step fm; step fm; step fm; finish

-- Inner loop repeated for even c: (a, 0, 2*k, d+1) →* (a+3*k, 0, 0, d+1+k)
theorem inner_loop_even : ⟨a, 0, 2*k, d+1⟩ [fm]⊢* ⟨a+3*k, 0, 0, d+1+k⟩ := by
  induction k generalizing a d with
  | zero => exists 0
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by omega]
    apply stepStar_trans inner_step
    apply stepStar_trans (ih (a := a + 3) (d := d + 1))
    rw [show a + 3 + 3 * k = a + 3 * (k + 1) from by ring,
        show d + 1 + 1 + k = d + 1 + (k + 1) from by omega]
    finish

-- Inner loop for odd c: (a, 0, 2*k+1, d+1) →* (a+d+4*k+3, 2*d+2*k+3, 0, 0)
theorem inner_loop_odd : ⟨a, 0, 2*k+1, d+1⟩ [fm]⊢* ⟨a+d+4*k+3, 2*d+2*k+3, 0, 0⟩ := by
  induction k generalizing a d with
  | zero =>
    -- (a, 0, 1, d+1): rule 2 -> (a+1, 2, 1, d) -> rule 1 -> (a+2, 1, 0, d+1) -> rule 2 -> (a+3, 3, 0, d)
    step fm; step fm; step fm
    -- now at (a+3, 3, 0, d), apply d_expand
    apply stepStar_trans (d_expand (a := a + 3) (b := 3) (d := d))
    rw [show a + 3 + d = a + d + 4 * 0 + 3 from by ring,
        show 3 + 2 * d = 2 * d + 2 * 0 + 3 from by ring]
    finish
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega]
    apply stepStar_trans inner_step
    apply stepStar_trans (ih (a := a + 3) (d := d + 1))
    rw [show a + 3 + (d + 1) + 4 * k + 3 = a + d + 4 * (k + 1) + 3 from by ring,
        show 2 * (d + 1) + 2 * k + 3 = 2 * d + 2 * (k + 1) + 3 from by ring]
    finish

-- Phase B for even C: (0, 0, 2*(k+1), 0) →⁺ (4*k+3, 2*k+2, 0, 0)
theorem phase_b_even : ⟨0, 0, 2*(k+1), 0⟩ [fm]⊢⁺ ⟨4*k+3, 2*k+2, 0, 0⟩ := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by omega]
  step fm  -- rule 5: (1, 1, 2*k+1, 0)... wait (0,0,(2k+1)+1,0) -> (1,1,2k+1,0)
  -- but (1, 1, 2*k+1, 0): b>=1, c>=1 so rule 1: (2, 0, 2*k, 1)
  step fm  -- (2, 0, 2*k, 1)
  apply stepStar_trans (inner_loop_even (a := 2) (k := k) (d := 0))
  apply stepStar_trans (d_expand (a := 2 + 3 * k) (b := 0) (d := 1 + k))
  rw [show 2 + 3 * k + (1 + k) = 4 * k + 3 from by ring,
      show 0 + 2 * (1 + k) = 2 * k + 2 from by ring]
  finish

-- Phase B for odd C: (0, 0, 2*k+3, 0) →⁺ (4*k+5, 2*k+3, 0, 0)
theorem phase_b_odd : ⟨0, 0, 2*k+3, 0⟩ [fm]⊢⁺ ⟨4*k+5, 2*k+3, 0, 0⟩ := by
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by omega]
  step fm  -- rule 5: (1, 1, 2*k+2, 0)
  -- (1, 1, 2*k+2, 0): b>=1, c>=1 so rule 1: (2, 0, 2*k+1, 1)
  step fm  -- (2, 0, 2*k+1, 1)
  apply stepStar_trans (inner_loop_odd (a := 2) (k := k) (d := 0))
  rw [show 2 + 0 + 4 * k + 3 = 4 * k + 5 from by ring,
      show 2 * 0 + 2 * k + 3 = 2 * k + 3 from by ring]
  finish

-- Main cycle: (n+1, 0, 0, 0) →⁺ (3*n+2, 0, 0, 0)
theorem main_cycle (n : ℕ) : ⟨n+1, 0, 0, 0⟩ [fm]⊢⁺ ⟨3*n+2, 0, 0, 0⟩ := by
  -- Phase A: (n+1, 0, 0, 0) →* (0, 0, 3*n+3, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 3 * (n + 1), 0⟩)
  · have h := @a_to_c 0 (n+1) 0
    simp at h; exact h
  -- Now at (0, 0, 3*(n+1), 0). Split on parity of n.
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n even: n = m + m, 3*(m+m+1) = 2*(3*m)+3 (odd)
    subst hm
    have : 3 * (m + m + 1) = 2 * (3 * m) + 3 := by ring
    rw [this]
    apply stepPlus_stepStar_stepPlus (phase_b_odd (k := 3 * m))
    rw [show 4 * (3 * m) + 5 = (3 * (m + m) + 2) + (2 * (3 * m) + 3) from by ring]
    exact ab_drain
  · -- n odd: n = 2*m+1, 3*(2*m+1+1) = 2*((3*m+2)+1) (even)
    subst hm
    have : 3 * (2 * m + 1 + 1) = 2 * ((3 * m + 2) + 1) := by ring
    rw [this]
    apply stepPlus_stepStar_stepPlus (phase_b_even (k := 3 * m + 2))
    rw [show 4 * (3 * m + 2) + 3 = (3 * (2 * m + 1) + 2) + (2 * (3 * m + 2) + 2) from by ring]
    exact ab_drain

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0⟩)
  · finish
  apply progress_nonhalt_simple (fm := fm) (C := fun n ↦ ⟨n+1, 0, 0, 0⟩) (i₀ := 0)
  intro n
  exact ⟨3*n+1, by rw [show 3 * n + 1 + 1 = 3 * n + 2 from by omega]; exact main_cycle n⟩
