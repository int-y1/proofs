import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1990: [99/35, 5/39, 14/3, 13/11, 363/2]

Vector representation:
```
 0  2 -1 -1  1  0
 0 -1  1  0  0 -1
 1 -1  0  1  0  0
 0  0  0  0 -1  1
-1  1  0  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1990

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e+2, f⟩
  | _ => none

-- R4 chain: (a, 0, 0, D, e+k, f) →* (a, 0, 0, D, e, f+k)
theorem e_to_f : ∀ k, ⟨a, (0 : ℕ), (0 : ℕ), D, e + k, f⟩ [fm]⊢*
    ⟨a, 0, 0, D, e, f + k⟩ := by
  intro k; induction' k with k ih generalizing e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (e := e) (f := f + 1))
    ring_nf; finish

-- R1+R2 loop: (a, b, 1, d+k, e, f+k) →* (a, b+k, 1, d, e+k, f)
theorem r1r2_loop : ∀ k, ⟨a, b, (1 : ℕ), d + k, e, f + k⟩ [fm]⊢*
    ⟨a, b + k, 1, d, e + k, f⟩ := by
  intro k; induction' k with k ih generalizing b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

-- R2 drain: (a, b+k, c, 0, e, k) →* (a, b, c+k, 0, e, 0)
theorem r2_drain : ∀ k, ⟨a, b + k, c, (0 : ℕ), e, k⟩ [fm]⊢*
    ⟨a, b, c + k, 0, e, 0⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (c := c + 1))
    ring_nf; finish

-- R1+R3 loop: (a, b, c+k, 1, e, 0) →* (a+k, b+k, c, 1, e+k, 0)
theorem r1r3_loop : ∀ k, ⟨a, b, c + k, (1 : ℕ), e, (0 : ℕ)⟩ [fm]⊢*
    ⟨a + k, b + k, c, 1, e + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c e
  · exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih (c := c + 1))
    step fm; step fm; ring_nf; finish

-- R3 drain: (a, b+k, 0, d, e, 0) →* (a+k, b, 0, d+k, e, 0)
theorem r3_drain : ∀ k, ⟨a, b + k, (0 : ℕ), d, e, (0 : ℕ)⟩ [fm]⊢*
    ⟨a + k, b, 0, d + k, e, 0⟩ := by
  intro k; induction' k with k ih generalizing a b d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (d := d + 1))
    ring_nf; finish

theorem main_star : ⟨a + 1, (0 : ℕ), (0 : ℕ), d + 1, 2 * d + 2, (0 : ℕ)⟩ [fm]⊢*
    ⟨a + 2 * d + 3, 0, 0, d + 2, 2 * d + 4, 0⟩ := by
  -- Phase 1: R4 chain
  rw [show 2 * d + 2 = 0 + (2 * d + 2) from by ring]
  apply stepStar_trans (e_to_f (2 * d + 2) (a := a + 1) (D := d + 1) (e := 0) (f := 0))
  rw [show (0 : ℕ) + (2 * d + 2) = 2 * d + 2 from by ring]
  -- Phase 2: R5
  step fm
  -- Phase 3: R2
  step fm
  -- Now at (a, 0, 1, d+1, 2, 2*d+1)
  -- Phase 4: R1+R2 loop (d+1 pairs)
  rw [show d + 1 = 0 + (d + 1) from by ring,
      show 2 * d + 1 = d + (d + 1) from by ring]
  apply stepStar_trans (r1r2_loop (d + 1) (a := a) (b := 0) (d := 0) (e := 2) (f := d))
  rw [show 0 + (d + 1) = d + 1 from by ring,
      show 2 + (d + 1) = d + 3 from by ring]
  -- Now at (a, d+1, 1, 0, d+3, d)
  -- Phase 5: R2 drain (d steps)
  rw [show d + 1 = 1 + d from by ring]
  apply stepStar_trans (r2_drain d (a := a) (b := 1) (c := 1) (e := d + 3))
  rw [show 1 + d = d + 1 from by ring]
  -- Now at (a, 1, d+1, 0, d+3, 0)
  -- Phase 6: R3
  step fm
  -- Now at (a+1, 0, d+1, 1, d+3, 0)
  -- Phase 7: R1+R3 loop (d pairs)
  rw [show d + 1 = 1 + d from by ring]
  apply stepStar_trans (r1r3_loop d (a := a + 1) (b := 0) (c := 1) (e := d + 3))
  rw [show a + 1 + d = a + d + 1 from by ring,
      show d + 3 + d = 2 * d + 3 from by ring]
  -- Now at (a+d+1, d, 1, 1, 2d+3, 0)
  -- Phase 8: R1
  step fm
  -- Now at (a+d+1, d+2, 0, 0, 2d+4, 0)
  rw [show 2 * d + 3 + 1 = 2 * d + 4 from by ring]
  -- Phase 9: R3 drain (d+2 steps)
  rw [show d + 2 = 0 + (d + 2) from by ring]
  apply stepStar_trans (r3_drain (d + 2) (a := a + d + 1) (b := 0) (d := 0) (e := 2 * d + 4))
  ring_nf; finish

theorem main_trans : ⟨a + 1, (0 : ℕ), (0 : ℕ), d + 1, 2 * d + 2, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨a + 2 * d + 3, 0, 0, d + 2, 2 * d + 4, 0⟩ := by
  apply stepStar_stepPlus main_star
  intro h
  have : a + 1 = a + 2 * d + 3 := congrArg (fun q : Q => q.1) h
  omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 2, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, d⟩ ↦ ⟨a + 1, 0, 0, d + 1, 2 * d + 2, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩
  exact ⟨⟨a + 2 * d + 2, d + 1⟩, main_trans⟩
