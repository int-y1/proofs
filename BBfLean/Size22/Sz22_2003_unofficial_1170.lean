import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1170: [5/6, 49/2, 2/385, 33/7, 20/3]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 1  0 -1 -1 -1
 0  1  0 -1  1
 2 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1170

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

-- Phase 1: R4 chain. Transfer d to b and e.
theorem d_to_be : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

-- Phase 2a: R5,R1,R1 chain. Each round moves 3 from b to c.
theorem r5r1r1_round : ⟨0, b + 3, c, 0, e⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  step fm; step fm; step fm; finish

theorem r5r1r1_chain : ∀ k, ⟨0, b + 3 * k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (b := b + 3))
    apply stepStar_trans r5r1r1_round
    rw [show c + 3 * k + 3 = c + 3 * (k + 1) from by ring]
    finish

-- Phase 2b: tail for D ≡ 2 mod 3.
theorem r5r1_tail2 : ⟨0, 2, c, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + 2, 2, e⟩ := by
  step fm; step fm; step fm; finish

-- Phase 2c: tail for D ≡ 1 mod 3.
theorem r5_tail1 : ⟨0, 1, c, 0, e⟩ [fm]⊢⁺ ⟨0, 0, c + 1, 4, e⟩ := by
  step fm; step fm; step fm; finish

-- Phase 3: R3/R2 chain.
theorem r3r2_chain : ∀ k, ⟨0, 0, c + k, d + 1, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k + 1, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- Combined: from (0, D, 0, 0, e), do r5r1r1 chain + tail2, yielding (0, 0, D, 2, e)
-- for D = 3*m + 2
theorem phase2_mod2 : ⟨0, 3 * m + 2, 0, 0, e⟩ [fm]⊢⁺ ⟨0, 0, 3 * m + 2, 2, e⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 3 * m + 2 = 2 + 3 * m from by ring]
    exact r5r1r1_chain m (b := 2) (c := 0)
  rw [show 0 + 3 * m = 3 * m from by ring]
  apply stepPlus_stepStar_stepPlus r5r1_tail2
  rw [show 3 * m + 2 = 3 * m + 2 from rfl]; finish

-- Combined: from (0, D, 0, 0, e), do r5r1r1 chain + tail1, yielding (0, 0, D, 4, e)
-- for D = 3*m + 1
theorem phase2_mod1 : ⟨0, 3 * m + 1, 0, 0, e⟩ [fm]⊢⁺ ⟨0, 0, 3 * m + 1, 4, e⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show 3 * m + 1 = 1 + 3 * m from by ring]
    exact r5r1r1_chain m (b := 1) (c := 0)
  rw [show 0 + 3 * m = 3 * m from by ring]
  apply stepPlus_stepStar_stepPlus r5_tail1
  rw [show 3 * m + 1 = 3 * m + 1 from rfl]; finish

-- Half-transition 1: (0, 0, 0, 6n+2, 0) ⊢⁺ (0, 0, 0, 6n+4, 0)
theorem half1 : ⟨0, 0, 0, 6 * n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 4, 0⟩ := by
  -- Phase 1: d_to_be
  have h1 : ⟨0, 0, 0, 6 * n + 2, 0⟩ [fm]⊢* ⟨0, 6 * n + 2, 0, 0, 6 * n + 2⟩ := by
    rw [show 6 * n + 2 = 0 + (6 * n + 2) from by ring]
    exact d_to_be (6 * n + 2) (b := 0) (d := 0) (e := 0)
  -- Phase 2: phase2_mod2 with m = 2*n
  have h2 : ⟨0, 6 * n + 2, 0, 0, 6 * n + 2⟩ [fm]⊢⁺ ⟨0, 0, 6 * n + 2, 2, 6 * n + 2⟩ := by
    rw [show 6 * n + 2 = 3 * (2 * n) + 2 from by ring]
    exact phase2_mod2 (m := 2 * n)
  -- Phase 3: r3r2_chain
  have h3 : ⟨0, 0, 6 * n + 2, 2, 6 * n + 2⟩ [fm]⊢* ⟨0, 0, 0, 6 * n + 4, 0⟩ := by
    rw [show 6 * n + 2 = 0 + (6 * n + 2) from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (r3r2_chain (6 * n + 2) (c := 0) (d := 1) (e := 0))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)

-- Half-transition 2: (0, 0, 0, 6n+4, 0) ⊢⁺ (0, 0, 0, 6(n+1)+2, 0)
theorem half2 : ⟨0, 0, 0, 6 * n + 4, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * (n + 1) + 2, 0⟩ := by
  -- Phase 1: d_to_be
  have h1 : ⟨0, 0, 0, 6 * n + 4, 0⟩ [fm]⊢* ⟨0, 6 * n + 4, 0, 0, 6 * n + 4⟩ := by
    rw [show 6 * n + 4 = 0 + (6 * n + 4) from by ring]
    exact d_to_be (6 * n + 4) (b := 0) (d := 0) (e := 0)
  -- Phase 2: phase2_mod1 with m = 2*n+1
  have h2 : ⟨0, 6 * n + 4, 0, 0, 6 * n + 4⟩ [fm]⊢⁺ ⟨0, 0, 6 * n + 4, 4, 6 * n + 4⟩ := by
    rw [show 6 * n + 4 = 3 * (2 * n + 1) + 1 from by ring]
    exact phase2_mod1 (m := 2 * n + 1)
  -- Phase 3: r3r2_chain
  have h3 : ⟨0, 0, 6 * n + 4, 4, 6 * n + 4⟩ [fm]⊢* ⟨0, 0, 0, 6 * (n + 1) + 2, 0⟩ := by
    rw [show 6 * n + 4 = 0 + (6 * n + 4) from by ring,
        show (4 : ℕ) = 3 + 1 from by ring]
    apply stepStar_trans (r3r2_chain (6 * n + 4) (c := 0) (d := 3) (e := 0))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)

-- Main transition: C(n) ⊢⁺ C(n+1) where C(n) = (0, 0, 0, 6n+2, 0)
theorem main_trans : ⟨0, 0, 0, 6 * n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * (n + 1) + 2, 0⟩ :=
  stepPlus_trans half1 half2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 6 * n + 2, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans⟩
