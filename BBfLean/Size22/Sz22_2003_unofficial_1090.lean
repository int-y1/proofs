import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1090: [5/6, 3/35, 539/3, 4/77, 15/2]

Vector representation:
```
-1 -1  1  0  0
 0  1 -1 -1  0
 0 -1  0  2  1
 2  0  0 -1 -1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1090

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R3 burst: drain b when c = 0.
-- (0, b, 0, d, e) →* (0, 0, 0, d + 2*b, e + b)
theorem r3_burst : ∀ b, ⟨0, b, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * b, e + b⟩ := by
  intro b; induction' b with b ih generalizing d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 2) (e := e + 1))
    ring_nf; finish

-- R2 chain: drain n from c and d simultaneously.
-- (0, b, c+n, d+n, e) →* (0, b+n, c, d, e)
theorem r2_chain : ∀ n, ⟨0, b, c + n, d + n, e⟩ [fm]⊢* ⟨0, b + n, c, d, e⟩ := by
  intro n; induction' n with n ih generalizing b c d
  · exists 0
  · rw [show c + (n + 1) = (c + n) + 1 from by ring,
        show d + (n + 1) = (d + n) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R1/R5 alternation: drain a (even) into c.
-- (2*k, 1, c, 0, 0) →* (0, 1, c + 2*k, 0, 0)
theorem r15_chain : ∀ k, ⟨2 * k, 1, c, 0, 0⟩ [fm]⊢* ⟨0, 1, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

-- R4 chain: drain d and e into a.
-- (a, 0, 0, d+1, d) →* (a + 2*d, 0, 0, 1, 0)
theorem r4_chain : ∀ d, ⟨a, 0, 0, d + 1, d⟩ [fm]⊢* ⟨a + 2 * d, 0, 0, 1, 0⟩ := by
  intro d; induction' d with d ih generalizing a
  · exists 0
  · rcases a with _ | a
    · step fm
      apply stepStar_trans (ih (a := 2))
      ring_nf; finish
    · step fm
      apply stepStar_trans (ih (a := a + 3))
      ring_nf; finish

-- General interleave: the R2/R3 interleaving phase.
-- (0, b, c, d+1, e) →* (0, 0, 0, c + d + 2*b + 1, c + e + b)
-- Proof by induction on c.
theorem gen_interleave : ∀ c, ∀ b d e, ⟨0, b, c, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, c + d + 2 * b + 1, c + e + b⟩ := by
  intro c; induction' c with c ih <;> intro b d e
  · -- c = 0: just R3 burst
    rw [show 0 + d + 2 * b + 1 = (d + 1) + 2 * b from by ring,
        show 0 + e + b = e + b from by ring]
    exact r3_burst b
  · -- c + 1: R2 fires first
    step fm
    rcases d with _ | d
    · -- d = 0: R3 fires next (need case split on c for step fm)
      have hstep : fm (0, b + 1, c, 0, e) = some (0, b, c, 2, e + 1) := by
        rcases c with _ | c <;> rfl
      apply stepStar_trans (step_stepStar hstep)
      apply stepStar_trans (ih b 1 (e + 1))
      ring_nf; finish
    · -- d + 1: IH directly
      apply stepStar_trans (ih (b + 1) d e)
      ring_nf; finish

-- Phase A: initial steps converting a to c.
-- (2*k + 2, 0, 0, 1, 0) ⊢⁺ (0, 0, 2*k + 1, 2, 1)
theorem phase_a : ⟨2 * k + 2, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * k + 1, 2, 1⟩ := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm  -- R5: (2*k+1, 1, 1, 1, 0)
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  step fm  -- R1: (2*k, 0, 2, 1, 0)
  have hstep_r2 : fm (2 * k, 0, 2, 1, 0) = some (2 * k, 1, 1, 0, 0) := by
    rcases k with _ | k <;> rfl
  apply stepStar_trans (step_stepStar hstep_r2)
  apply stepStar_trans (r15_chain k (c := 1))
  rw [show 1 + 2 * k = (2 * k + 1) from by ring]
  step fm  -- R3: (0, 0, 2*k+1, 2, 1)
  finish

-- Main transition: (2*k + 2, 0, 0, 1, 0) ⊢⁺ (4*k + 4, 0, 0, 1, 0)
theorem main_trans (k : ℕ) : ⟨2 * k + 2, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨4 * k + 4, 0, 0, 1, 0⟩ := by
  apply stepPlus_stepStar_stepPlus phase_a
  have hb := gen_interleave (2 * k + 1) 0 1 1
  rw [show (2 * k + 1) + 1 + 2 * 0 + 1 = 2 * k + 3 from by ring,
      show (2 * k + 1) + 1 + 0 = 2 * k + 2 from by ring] at hb
  have hc : ⟨0, 0, 0, 2 * k + 3, 2 * k + 2⟩ [fm]⊢* ⟨4 * k + 4, 0, 0, 1, 0⟩ := by
    rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
    apply stepStar_trans (r4_chain (2 * k + 2) (a := 0))
    ring_nf; finish
  exact stepStar_trans hb hc

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 1, 0⟩)
  · execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨2 * k + 2, 0, 0, 1, 0⟩) 1
  intro k
  exact ⟨2 * k + 1, by
    show ⟨2 * k + 2, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨2 * (2 * k + 1) + 2, 0, 0, 1, 0⟩
    rw [show 2 * (2 * k + 1) + 2 = 4 * k + 4 from by ring]
    exact main_trans k⟩

end Sz22_2003_unofficial_1090
