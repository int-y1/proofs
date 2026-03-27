import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #642: [35/6, 143/2, 4/55, 3/7, 75/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  1  2  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_642

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+2, d, e, f⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction k with
  | zero => intro b; exists 0
  | succ k ih =>
    intro b
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- R3,R2,R2 drain: (0,0,c+k,D,e+k,F) ⊢* (0,0,c,D,e+2k,F+2k)
theorem r3r2r2_drain : ∀ k c e F, ⟨0, 0, c + k, D, e + k, F⟩ [fm]⊢* ⟨0, 0, c, D, e + 2 * k, F + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro c e F; exists 0
  | succ k ih =>
    intro c e F
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + k + 1 + 1 = (e + 2) + k from by ring,
        show F + 1 + 1 = F + 2 from by ring]
    apply stepStar_trans (ih c (e + 2) (F + 2))
    ring_nf; finish

-- R1,R1,R3 interleave: (2,b+2k,c,d,e+k,f) ⊢* (2,b,c+k,d+2k,e,f)
theorem r1r1r3_chain : ∀ k c d e, ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

-- Base case: d=0
theorem base0 : ⟨0, 0, 0, 0, 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 3, f + 5⟩ := by
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  step fm; step fm; finish

-- Transition for odd d (d = 2m+1, m >= 0):
-- (0,0,0,2m+1,4m+3,F+1) ⊢⁺ (0,0,0,2m+2,4m+5,F+2m+6)
theorem trans_odd : ⟨0, 0, 0, 2 * m + 1, 4 * m + 3, F + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 2, 4 * m + 5, F + 2 * m + 6⟩ := by
  -- Phase 1: R4*(2m+1)
  rw [show (2 * m + 1 : ℕ) = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b _ _)
  simp only [Nat.zero_add]
  -- Phase 2: R5, R3 (2 steps)
  step fm
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring]
  step fm
  -- Now at (2, 2m+2, 1, 0, 4m+2, F)
  -- Phase 3: R1,R1,R3 chain (m+1 rounds)
  rw [show (2 * m + 2 : ℕ) = 0 + 2 * (m + 1) from by ring,
      show (4 * m + 2 : ℕ) = (3 * m + 1) + (m + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (m + 1) 1 0 (3 * m + 1))
  -- Now at (2, 0, m+2, 2m+2, 3m+1, F)
  -- Phase 4: R2, R2
  step fm; step fm
  -- Now at (0, 0, m+2, 2m+2, 3m+3, F+2)
  rw [show 1 + (m + 1) = 0 + (m + 2) from by ring,
      show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
      show 3 * m + 1 + 1 + 1 = (2 * m + 1) + (m + 2) from by ring,
      show F + 1 + 1 = F + 2 from by ring]
  -- Phase 5: drain (m+2 rounds)
  apply stepStar_trans (r3r2r2_drain (m + 2) 0 (2 * m + 1) (F + 2))
  ring_nf; finish

-- Transition for even d >= 2 (d = 2m+2, m >= 0):
-- (0,0,0,2m+2,4m+5,F+1) ⊢⁺ (0,0,0,2m+3,4m+7,F+2m+7)
theorem trans_even : ⟨0, 0, 0, 2 * m + 2, 4 * m + 5, F + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 3, 4 * m + 7, F + 2 * m + 7⟩ := by
  -- Phase 1: R4*(2m+2)
  rw [show (2 * m + 2 : ℕ) = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b _ _)
  simp only [Nat.zero_add]
  -- Phase 2: R5, R3 (2 steps)
  step fm
  rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring]
  step fm
  -- Now at (2, 2m+3, 1, 0, 4m+4, F)
  -- Phase 3: R1,R1,R3 chain (m+1 rounds)
  rw [show (2 * m + 3 : ℕ) = 1 + 2 * (m + 1) from by ring,
      show (4 * m + 4 : ℕ) = (3 * m + 3) + (m + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (m + 1) 1 0 (3 * m + 3))
  -- Now at (2, 1, m+2, 2m+2, 3m+3, F)
  -- Phase 4: R1
  step fm
  -- Now at (1, 0, m+3, 2m+3, 3m+3, F)
  -- Phase 5: R2
  step fm
  -- Now at (0, 0, m+3, 2m+3, 3m+4, F+1)
  rw [show 1 + (m + 1) + 1 = 0 + (m + 3) from by ring,
      show 0 + 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
      show 3 * m + 3 + 1 = (2 * m + 1) + (m + 3) from by ring]
  -- Phase 6: drain (m+3 rounds)
  apply stepStar_trans (r3r2r2_drain (m + 3) 0 (2 * m + 1) (F + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, 0, n, 2 * n + 1, f + 1⟩) ⟨0, 0⟩
  intro ⟨n, f⟩
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2m (even)
    subst hm
    rcases m with _ | m
    · -- n = 0
      exact ⟨⟨1, f + 4⟩, by
        show (0, 0, 0, 0, 1, f + 1) [fm]⊢⁺ (0, 0, 0, 1, 3, f + 5)
        exact base0⟩
    · -- n = 2(m+1) = 2m+2
      exact ⟨⟨2 * m + 3, f + 2 * m + 6⟩, by
        show (0, 0, 0, m + 1 + (m + 1), 2 * (m + 1 + (m + 1)) + 1, f + 1) [fm]⊢⁺
          (0, 0, 0, 2 * m + 3, 2 * (2 * m + 3) + 1, f + 2 * m + 6 + 1)
        rw [show m + 1 + (m + 1) = 2 * m + 2 from by ring,
            show 2 * (2 * m + 2) + 1 = 4 * m + 5 from by ring,
            show 2 * (2 * m + 3) + 1 = 4 * m + 7 from by ring,
            show f + 2 * m + 6 + 1 = f + 2 * m + 7 from by ring]
        exact trans_even⟩
  · -- n = 2m+1 (odd)
    subst hm
    exact ⟨⟨2 * m + 2, f + 2 * m + 5⟩, by
      show (0, 0, 0, 2 * m + 1, 2 * (2 * m + 1) + 1, f + 1) [fm]⊢⁺
        (0, 0, 0, 2 * m + 2, 2 * (2 * m + 2) + 1, f + 2 * m + 5 + 1)
      rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring,
          show 2 * (2 * m + 2) + 1 = 4 * m + 5 from by ring,
          show f + 2 * m + 5 + 1 = f + 2 * m + 6 from by ring]
      exact trans_odd⟩
