import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #786: [35/6, 56/55, 143/2, 3/7, 5/13]

Vector representation:
```
-1 -1  1  1  0  0
 3  0 -1  1 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_786

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih generalizing a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (e := e + 1) (f := f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

theorem r2_chain : ∀ k, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 3 * k, 0, c, d + k, e, f⟩ := by
  intro k; induction' k with k ih generalizing a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 3) (d := d + 1))
    ring_nf; finish

theorem r1_chain : ∀ k, ⟨a + k, b + k, c, d, e, f⟩ [fm]⊢* ⟨a, b, c + k, d + k, e, f⟩ := by
  intro k; induction' k with k ih generalizing a b c d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1) (d := d + 1))
    ring_nf; finish

-- Interleaved phase: k rounds of (R1x3 + R2).
-- (3, 3*k+b, c, d, e+k, f) →* (3, b, c+2*k, d+4*k, e, f)
theorem interleave : ∀ k, ⟨3, 3 * k + b, c, d, e + k, f⟩ [fm]⊢* ⟨3, b, c + 2 * k, d + 4 * k, e, f⟩ := by
  intro k; induction' k with k ih generalizing b c d e f
  · simp; exists 0
  · rw [show 3 * (k + 1) + b = (3 * k + (b + 3)) from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 3) (e := e + 1))
    -- Now at (3, b+3, c+2*k, d+4*k, e+1, f)
    -- R1 x 3
    apply stepStar_trans
    · show ⟨0 + 3, b + 3, c + 2 * k, d + 4 * k, e + 1, f⟩ [fm]⊢*
           ⟨0, b, (c + 2 * k) + 3, (d + 4 * k) + 3, e + 1, f⟩
      exact r1_chain 3
    -- R2: c+2k+3 = (c+2k+2)+1, e+1 = e+1
    rw [show (c + 2 * k) + 3 = (c + 2 * k + 2) + 1 from by ring]
    step fm
    ring_nf; finish

-- Phase E case d mod 3 = 0: d = 3*k.
-- Input: (3, 3k+3, 0, 1, e+3k+5, 6k+6)
-- Output: (6k+9, 0, 0, 6k+7, e+2, 6k+6)
theorem phase_e_mod0 (k : ℕ) :
    ⟨3, 3 * k + 3, 0, 1, e + 3 * k + 5, 6 * k + 6⟩ [fm]⊢*
    ⟨6 * k + 9, 0, 0, 6 * k + 7, e + 2, 6 * k + 6⟩ := by
  rw [show 3 * k + 3 = 3 * (k + 1) + 0 from by ring,
      show e + 3 * k + 5 = (e + 2 * k + 4) + (k + 1) from by ring]
  apply stepStar_trans (interleave (k + 1) (b := 0) (c := 0) (d := 1) (e := e + 2 * k + 4) (f := 6 * k + 6))
  -- Now at (3, 0, 2k+2, 4k+5, e+2k+4, 6k+6)
  rw [show (0 : ℕ) + 2 * (k + 1) = 0 + (2 * k + 2) from by ring,
      show (1 : ℕ) + 4 * (k + 1) = 4 * k + 5 from by ring,
      show e + 2 * k + 4 = (e + 2) + (2 * k + 2) from by ring]
  apply stepStar_trans (r2_chain (2 * k + 2) (a := 3) (c := 0) (d := 4 * k + 5) (e := e + 2) (f := 6 * k + 6))
  ring_nf; finish

-- Phase E case d mod 3 = 1: d = 3*k+1.
-- Input: (3, 3k+4, 0, 1, e+3k+6, 6k+8)
-- After k+1 interleave rounds: (3, 1, 2k+2, 4k+5, e+2k+5, 6k+8)
-- R1 x 1: (2, 0, 2k+3, 4k+6, e+2k+5, 6k+8)
-- R2 chain x (2k+3): (2+3*(2k+3), 0, 0, 4k+6+2k+3, e+2k+5-(2k+3), 6k+8)
--   = (6k+11, 0, 0, 6k+9, e+2, 6k+8)
theorem phase_e_mod1 (k : ℕ) :
    ⟨3, 3 * k + 4, 0, 1, e + 3 * k + 6, 6 * k + 8⟩ [fm]⊢*
    ⟨6 * k + 11, 0, 0, 6 * k + 9, e + 2, 6 * k + 8⟩ := by
  rw [show 3 * k + 4 = 3 * (k + 1) + 1 from by ring,
      show e + 3 * k + 6 = (e + 2 * k + 5) + (k + 1) from by ring]
  apply stepStar_trans (interleave (k + 1) (b := 1) (c := 0) (d := 1) (e := e + 2 * k + 5) (f := 6 * k + 8))
  -- Now at (3, 1, 2k+2, 4k+5, e+2k+5, 6k+8)
  -- R1 x 1: need to show (3, 1, ...) = (2+1, 0+1, ...)
  apply stepStar_trans
  · show ⟨2 + 1, 0 + 1, 0 + 2 * (k + 1), 1 + 4 * (k + 1), e + 2 * k + 5, 6 * k + 8⟩ [fm]⊢*
         ⟨2, 0, (0 + 2 * (k + 1)) + 1, (1 + 4 * (k + 1)) + 1, e + 2 * k + 5, 6 * k + 8⟩
    exact r1_chain 1
  -- Now at (2, 0, 2k+3, 4k+6, e+2k+5, 6k+8)
  rw [show (0 + 2 * (k + 1)) + 1 = 0 + (2 * k + 3) from by ring,
      show (1 + 4 * (k + 1)) + 1 = 4 * k + 6 from by ring,
      show e + 2 * k + 5 = (e + 2) + (2 * k + 3) from by ring]
  apply stepStar_trans (r2_chain (2 * k + 3) (a := 2) (c := 0) (d := 4 * k + 6) (e := e + 2) (f := 6 * k + 8))
  ring_nf; finish

-- Phase E case d mod 3 = 2: d = 3*k+2.
-- Input: (3, 3k+5, 0, 1, e+3k+7, 6k+10)
-- After k+1 interleave rounds: (3, 2, 2k+2, 4k+5, e+2k+6, 6k+10)
-- R1 x 2: (1, 0, 2k+4, 4k+7, e+2k+6, 6k+10)
-- R2 chain x (2k+4): (1+3*(2k+4), 0, 0, 4k+7+2k+4, e+2k+6-(2k+4), 6k+10)
--   = (6k+13, 0, 0, 6k+11, e+2, 6k+10)
theorem phase_e_mod2 (k : ℕ) :
    ⟨3, 3 * k + 5, 0, 1, e + 3 * k + 7, 6 * k + 10⟩ [fm]⊢*
    ⟨6 * k + 13, 0, 0, 6 * k + 11, e + 2, 6 * k + 10⟩ := by
  rw [show 3 * k + 5 = 3 * (k + 1) + 2 from by ring,
      show e + 3 * k + 7 = (e + 2 * k + 6) + (k + 1) from by ring]
  apply stepStar_trans (interleave (k + 1) (b := 2) (c := 0) (d := 1) (e := e + 2 * k + 6) (f := 6 * k + 10))
  -- Now at (3, 2, 2k+2, 4k+5, e+2k+6, 6k+10)
  -- R1 x 2
  apply stepStar_trans
  · show ⟨1 + 2, 0 + 2, 0 + 2 * (k + 1), 1 + 4 * (k + 1), e + 2 * k + 6, 6 * k + 10⟩ [fm]⊢*
         ⟨1, 0, (0 + 2 * (k + 1)) + 2, (1 + 4 * (k + 1)) + 2, e + 2 * k + 6, 6 * k + 10⟩
    exact r1_chain 2
  -- Now at (1, 0, 2k+4, 4k+7, e+2k+6, 6k+10)
  rw [show (0 + 2 * (k + 1)) + 2 = 0 + (2 * k + 4) from by ring,
      show (1 + 4 * (k + 1)) + 2 = 4 * k + 7 from by ring,
      show e + 2 * k + 6 = (e + 2) + (2 * k + 4) from by ring]
  apply stepStar_trans (r2_chain (2 * k + 4) (a := 1) (c := 0) (d := 4 * k + 7) (e := e + 2) (f := 6 * k + 10))
  ring_nf; finish

-- Main transition: (d+5, 0, 0, d+3, e+1, d+2) →⁺ (2*d+9, 0, 0, 2*d+7, e+2, 2*d+6)
theorem main_trans : ⟨d + 5, 0, 0, d + 3, e + 1, d + 2⟩ [fm]⊢⁺ ⟨2 * d + 9, 0, 0, 2 * d + 7, e + 2, 2 * d + 6⟩ := by
  -- Phase A: R3 x (d+5)
  apply stepStar_stepPlus_stepPlus
  · rw [show d + 5 = 0 + (d + 5) from by ring]
    exact r3_chain (d + 5) (a := 0) (d := d + 3) (e := e + 1) (f := d + 2)
  -- State: (0, 0, 0, d+3, e+d+6, 2d+7)
  -- Phase B: R4 x (d+3)
  rw [show e + 1 + (d + 5) = e + d + 6 from by ring,
      show (d + 2) + (d + 5) = 2 * d + 7 from by ring,
      show d + 3 = 0 + (d + 3) from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact r4_chain (d + 3) (b := 0) (d := 0) (e := e + d + 6) (f := 2 * d + 7)
  -- State: (0, d+3, 0, 0, e+d+6, 2d+7)
  rw [show (0 : ℕ) + (d + 3) = d + 3 from by ring,
      show 2 * d + 7 = (2 * d + 6) + 1 from by ring,
      show e + d + 6 = (e + d + 5) + 1 from by ring]
  -- Phase C: R5
  step fm
  -- State: (0, d+3, 1, 0, (e+d+5)+1, 2d+6)
  -- Phase D: R2
  step fm
  -- State: (3, d+3, 0, 1, e+d+5, 2d+6)
  -- Phase E: dispatch on d mod 3
  obtain ⟨k, rfl | rfl | rfl⟩ : ∃ k, d = 3 * k ∨ d = 3 * k + 1 ∨ d = 3 * k + 2 := ⟨d / 3, by omega⟩
  · rw [show 3 * k + 3 = 3 * k + 3 from rfl,
        show e + 3 * k + 5 = e + 3 * k + 5 from rfl,
        show 2 * (3 * k) + 6 = 6 * k + 6 from by ring]
    apply stepStar_trans (phase_e_mod0 k (e := e))
    ring_nf; finish
  · rw [show 3 * k + 1 + 3 = 3 * k + 4 from by ring,
        show e + (3 * k + 1) + 5 = e + 3 * k + 6 from by ring,
        show 2 * (3 * k + 1) + 6 = 6 * k + 8 from by ring]
    apply stepStar_trans (phase_e_mod1 k (e := e))
    ring_nf; finish
  · rw [show 3 * k + 2 + 3 = 3 * k + 5 from by ring,
        show e + (3 * k + 2) + 5 = e + 3 * k + 7 from by ring,
        show 2 * (3 * k + 2) + 6 = 6 * k + 10 from by ring]
    apply stepStar_trans (phase_e_mod2 k (e := e))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 3, 1, 2⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨d + 5, 0, 0, d + 3, e + 1, d + 2⟩) ⟨0, 0⟩
  intro ⟨d, e⟩; exists ⟨2 * d + 4, e + 1⟩
  show ⟨d + 5, 0, 0, d + 3, e + 1, d + 2⟩ [fm]⊢⁺ ⟨(2 * d + 4) + 5, 0, 0, (2 * d + 4) + 3, (e + 1) + 1, (2 * d + 4) + 2⟩
  rw [show (2 * d + 4) + 5 = 2 * d + 9 from by ring,
      show (2 * d + 4) + 3 = 2 * d + 7 from by ring,
      show (e + 1) + 1 = e + 2 from by ring,
      show (2 * d + 4) + 2 = 2 * d + 6 from by ring]
  exact main_trans
