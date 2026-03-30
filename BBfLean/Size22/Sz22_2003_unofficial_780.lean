import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #780: [35/6, 55/2, 8/77, 3/5, 4/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  1
 3  0  0 -1 -1
 0  1 -1  0  0
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_780

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- R4 chain: move c to b (with d = 0)
theorem c_to_b : ∀ k b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction k with
  | zero => intro b c e; simp; exists 0
  | succ k ih =>
    intro b c e
    rw [Nat.add_succ c k]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

-- R3+R2x3 chain: each cycle applies R3 once then R2 three times.
-- From (0, 0, c, d+k, e+1) to (0, 0, c+3k, d, e+2k+1).
theorem r3r2_chain : ∀ k c d e, ⟨0, 0, c, d + k, e + 1⟩ [fm]⊢* ⟨0, 0, c + 3 * k, d, e + 2 * k + 1⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show e + 1 + 1 + 1 = (e + 2) + 1 from by ring,
        show d + k = d + k from rfl]
    apply stepStar_trans (ih (c + 3) d (e + 2))
    ring_nf; finish

-- Combined inner loop: from (3, b, c, d, f) reaches (0, 0, c+3d+3b+3, 0, 2d+b+f+3).
-- Requires b <= 2f+1 for the inductive step to work (ensures R3 can fire).
-- By strong induction on b with base cases b=0,1,2 and step b+3.
theorem inner_loop : ∀ b c d f, b ≤ 2 * f + 1 →
    ⟨3, b, c, d, f⟩ [fm]⊢* ⟨0, 0, c + 3 * d + 3 * b + 3, 0, 2 * d + b + f + 3⟩ := by
  intro b; induction b using Nat.strongRecOn with
  | _ b ih =>
    intro c d f hbf
    rcases b with _ | _ | _ | b
    · -- b = 0: R2x3 then R3+R2x3 chain
      step fm; step fm; step fm
      show ⟨0, 0, c + 3, d, f + 3⟩ [fm]⊢* _
      rw [show (f + 3 : ℕ) = (f + 2) + 1 from by ring,
          show (d : ℕ) = 0 + d from by ring]
      apply stepStar_trans (r3r2_chain d (c + 3) 0 (f + 2))
      ring_nf; finish
    · -- b = 1: R1 then R2x2 then R3+R2x3 chain
      step fm; step fm; step fm
      show ⟨0, 0, c + 3, d + 1, f + 2⟩ [fm]⊢* _
      rw [show (f + 2 : ℕ) = (f + 1) + 1 from by ring,
          show (d + 1 : ℕ) = 0 + (d + 1) from by ring]
      apply stepStar_trans (r3r2_chain (d + 1) (c + 3) 0 (f + 1))
      ring_nf; finish
    · -- b = 2: R1x2 then R2 then R3+R2x3 chain
      step fm; step fm; step fm
      show ⟨0, 0, c + 3, d + 2, f + 1⟩ [fm]⊢* _
      rw [show (f + 1 : ℕ) = f + 0 + 1 from by ring,
          show (d + 2 : ℕ) = 0 + (d + 2) from by ring]
      apply stepStar_trans (r3r2_chain (d + 2) (c + 3) 0 (f + 0))
      ring_nf; finish
    · -- b + 3: R1x3 then R3 then apply IH with b
      -- From constraint: b+3 <= 2f+1, so f >= 1. Write f = f'+1.
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      step fm; step fm; step fm
      show ⟨0, b, c + 3, d + 3, f' + 1⟩ [fm]⊢* _
      rw [show d + 3 = (d + 2) + 1 from by ring]
      step fm  -- R3: (3, b, c+3, d+2, f')
      apply stepStar_trans (ih b (by omega) (c + 3) (d + 2) f' (by omega))
      ring_nf; finish

-- Main transition: (0, 0, 2e+1, 0, e+1) ⊢⁺ (0, 0, 6e+5, 0, 3e+3)
theorem main_trans : ∀ e, ⟨0, 0, 2 * e + 1, 0, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 6 * e + 5, 0, 3 * e + 3⟩ := by
  intro e
  rcases e with _ | e
  · -- e = 0: direct computation
    execute fm 8
  · -- e + 1: R4 chain + R5 + R1x2 + R3 + inner_loop
    apply stepStar_stepPlus_stepPlus
    · -- R4 chain
      rw [show 2 * (e + 1) + 1 = 0 + (2 * e + 3) from by ring]
      exact c_to_b (2 * e + 3) 0 0 (e + 2)
    · -- R5 + R1x2 + R3 + inner_loop
      rw [show 0 + (2 * e + 3) = 2 * e + 3 from by ring]
      step fm  -- R5
      step fm  -- R1
      step fm  -- R1
      step fm  -- R3
      apply stepStar_trans (inner_loop (2 * e + 1) 2 1 e (by omega))
      ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨0, 0, 2 * e + 1, 0, e + 1⟩) 0
  intro e; refine ⟨3 * e + 2, ?_⟩
  rw [show 2 * (3 * e + 2) + 1 = 6 * e + 5 from by ring,
      show 3 * e + 2 + 1 = 3 * e + 3 from by ring]
  exact main_trans e
