import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #871: [4/15, 1/14, 33/2, 8575/11, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  0  0 -1  0
-1  1  0  0  1
 0  0  2  3 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_871

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d+3, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: drain e, adding 2 to c and 3 to d per step
-- (0, 0, c, d, e) →* (0, 0, c + 2*e, d + 3*e, 0)
theorem r4_drain : ∀ e, ⟨(0 : ℕ), 0, c, d, e⟩ [fm]⊢* ⟨0, 0, c + 2 * e, d + 3 * e, 0⟩ := by
  intro e; induction' e with e ih generalizing c d
  · simp; finish
  · step fm
    apply stepStar_trans (ih (c := c + 2) (d := d + 3))
    ring_nf; finish

-- Drain loop: (R5, R1, R2, R2) repeated k times
-- (0, 0, c+k, 3*k+d, 0) →* (0, 0, c, d, 0) when each iteration has d >= 1 at R5
-- More precisely: (0, 0, C+1+k, 3*k+D+1, 0) →* (0, 0, C+1, D+1, 0)
-- Actually simplest: (0, 0, c+1+k, 3*k+1, 0) →* (0, 0, c+1, 1, 0)
theorem drain_loop : ∀ k, ⟨(0 : ℕ), 0, c + 1 + k, 3 * k + 1, 0⟩ [fm]⊢* ⟨0, 0, c + 1, 1, 0⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [show c + 1 + (k + 1) = (c + 1 + k) + 1 from by ring,
        show 3 * (k + 1) + 1 = (3 * k + 1) + 3 from by ring]
    step fm  -- R5
    step fm  -- R1
    step fm  -- R2
    step fm  -- R2
    apply stepStar_trans (ih (c := c))
    ring_nf; finish

-- R3,R1 interleaved chain: needs a >= 1 and c >= 1 at each step
-- (a+1, 0, k+1, 0, e) →* (a+k+2, 0, 0, 0, e+k+1)
theorem r3r1_chain : ∀ k, ⟨a + 1, 0, k + 1, 0, e⟩ [fm]⊢* ⟨a + k + 2, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a e
  · step fm  -- R3: (a, 1, 1, 0, e+1)
    step fm  -- R1: (a+2, 0, 0, 0, e+1)
    ring_nf; finish
  · step fm  -- R3: (a, 1, k+2, 0, e+1)
    step fm  -- R1: (a+2, 0, k+1, 0, e+1)
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

-- R3 drain: (k, b, 0, 0, e) →* (0, b+k, 0, 0, e+k)
theorem r3_drain : ∀ k, ⟨k, b, 0, 0, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

-- Phase 2 inner loop body: (0, b+3, 0, 0, E+1) →⁺ (0, b+2, 0, 0, E+1)
theorem phase2_body : ⟨(0 : ℕ), b + 3, 0, 0, E + 1⟩ [fm]⊢⁺ ⟨0, b + 2, 0, 0, E + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Phase 2 loop: (0, k+2, 0, 0, E+1) →* (0, 2, 0, 0, E+1)
theorem phase2_loop : ∀ k, ⟨(0 : ℕ), k + 2, 0, 0, E + 1⟩ [fm]⊢* ⟨0, 2, 0, 0, E + 1⟩ := by
  intro k; induction' k with k ih
  · exists 0
  · rw [show k + 1 + 2 = (k + 2) + 1 from by ring,
        show (k + 2 + 1 : ℕ) = k + 3 from by ring]
    exact stepStar_trans (stepPlus_stepStar (phase2_body (b := k) (E := E))) ih

-- Phase 2 final: (0, 2, 0, 0, E+1) →⁺ (1, 0, 0, 0, E)
theorem phase2_final : ⟨(0 : ℕ), 2, 0, 0, E + 1⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, E⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Phase 2: (e+2, 0, 0, 0, e) →⁺ (1, 0, 0, 0, 2*e+1)
theorem phase2 : ⟨e + 2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2 * e + 1⟩ := by
  apply stepStar_stepPlus_stepPlus (r3_drain (e + 2) (b := 0) (e := e))
  rw [show (0 + (e + 2) : ℕ) = e + 2 from by ring,
      show e + (e + 2) = (2 * e + 1) + 1 from by ring]
  rw [show (e + 2 : ℕ) = e + 2 from rfl]
  apply stepStar_stepPlus_stepPlus (phase2_loop e (E := 2 * e + 1))
  exact phase2_final

-- Phase 1 for e=0: (1, 0, 0, 0, 0) →⁺ (2, 0, 0, 0, 0)
theorem phase1_e0 : (⟨1, 0, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨2, 0, 0, 0, 0⟩ := by
  execute fm 7

-- Phase 1 for e >= 1: (1, 0, 0, 0, e+1) →⁺ (e+3, 0, 0, 0, e+1)
theorem phase1 : (⟨1, 0, 0, 0, e + 1⟩ : Q) [fm]⊢⁺ ⟨e + 3, 0, 0, 0, e + 1⟩ := by
  step fm  -- R3
  step fm  -- R4
  step fm  -- R1
  step fm  -- R2
  step fm  -- R2
  -- Now at (0, 0, 1, 1, e+1)
  apply stepStar_trans (r4_drain (e + 1) (c := 1) (d := 1))
  -- Now at (0, 0, 1+2*(e+1), 1+3*(e+1), 0)
  rw [show 1 + 2 * (e + 1) = (e + 1) + 1 + (e + 1) from by ring,
      show 1 + 3 * (e + 1) = 3 * (e + 1) + 1 from by ring]
  apply stepStar_trans (drain_loop (e + 1) (c := e + 1))
  -- Now at (0, 0, (e+1)+1, 1, 0)
  step fm  -- R5: (0, 1, e+2, 0, 0)
  step fm  -- R1: (2, 0, e+1, 0, 0)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r1_chain e (a := 1) (e := 0))
  ring_nf; finish

-- Main transition: (1, 0, 0, 0, e) →⁺ (1, 0, 0, 0, 2*e+1)
theorem main_trans : (⟨1, 0, 0, 0, e⟩ : Q) [fm]⊢⁺ ⟨1, 0, 0, 0, 2 * e + 1⟩ := by
  rcases e with _ | e
  · apply stepPlus_stepStar_stepPlus phase1_e0
    exact stepPlus_stepStar (phase2 (e := 0))
  · apply stepPlus_stepStar_stepPlus phase1
    rw [show e + 3 = (e + 1) + 2 from by ring]
    exact stepPlus_stepStar (phase2 (e := e + 1))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨1, 0, 0, 0, e⟩) 0
  intro e; exists 2 * e + 1; exact main_trans

end Sz22_2003_unofficial_871
