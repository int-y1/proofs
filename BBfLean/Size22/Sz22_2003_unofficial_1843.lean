import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1843: [9/35, 1/198, 10/3, 11/5, 147/2]

Vector representation:
```
 0  2 -1 -1  0
-1 -2  0  0 -1
 1 -1  1  0  0
 0  0 -1  0  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1843

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+2, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- Phase 1: Drain e via 4-step rounds (R5, R3, R1, R2).
theorem drain : ∀ k, ⟨a + k, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih generalizing a d
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a := a) (d := d + 1))
    ring_nf; finish

-- Phase 2b: R1/R3 interleave draining d.
theorem interleave : ∀ k, ⟨a, b, 1, k + 1, 0⟩ [fm]⊢* ⟨a + k, b + k + 2, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · step fm; finish
  · rw [show (k : ℕ) + 1 + 1 = k + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (b := b + 1))
    ring_nf; finish

-- Phase 2c: R3 chain. Since b >= 1, R3 fires regardless of c.
-- We need simp [fm] because step fm can't handle symbolic c.
theorem r3_chain_step : ⟨a, b + 1, c, 0, 0⟩ [fm]⊢ ⟨a + 1, b, c + 1, 0, 0⟩ := by
  simp [fm]

theorem r3_chain : ∀ k, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + k, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · apply stepStar_trans (step_stepStar (r3_chain_step (a := a) (b := k) (c := c)))
    apply stepStar_trans (ih (a := a + 1) (c := c + 1))
    ring_nf; finish

-- Phase 3: R4 chain converting c to e.
theorem c_to_e : ∀ k, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing e
  · exists 0
  · step fm
    apply stepStar_trans (ih (e := e + 1))
    ring_nf; finish

-- Combined transition from (F+1, 0, 0, 3n, 0) through phases 2+3.
theorem tail (F n : ℕ) :
    ⟨F + 1, 0, 0, 3 * n, 0⟩ [fm]⊢⁺ ⟨6 * n + 5 + F, 0, 0, 0, 3 * n + 3⟩ := by
  step fm; step fm
  rw [show 3 * n + 2 = (3 * n + 1) + 1 from by ring]
  apply stepStar_trans (interleave (3 * n + 1) (a := F + 1) (b := 0))
  simp only [Nat.zero_add]
  rw [show F + 1 + (3 * n + 1) = F + 3 * n + 2 from by ring,
      show (3 * n + 1) + 2 = 3 * n + 3 from by ring]
  apply stepStar_trans (r3_chain (3 * n + 3) (a := F + 3 * n + 2) (c := 0))
  simp only [Nat.zero_add]
  rw [show F + 3 * n + 2 + (3 * n + 3) = 6 * n + 5 + F from by ring]
  apply stepStar_trans (c_to_e (3 * n + 3) (a := 6 * n + 5 + F) (e := 0))
  simp only [Nat.zero_add]; finish

-- Main transition composing drain + tail.
theorem main_trans (F n : ℕ) :
    ⟨3 * n + 1 + F, 0, 0, 0, 3 * n⟩ [fm]⊢⁺ ⟨6 * n + 5 + F, 0, 0, 0, 3 * n + 3⟩ := by
  rw [show 3 * n + 1 + F = (F + 1) + 3 * n from by ring]
  apply stepStar_stepPlus_stepPlus (drain (3 * n) (a := F + 1) (d := 0))
  rw [show (0 : ℕ) + 3 * n = 3 * n from by ring]
  exact tail F n

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, n⟩ ↦ ⟨3 * n + 1 + F, 0, 0, 0, 3 * n⟩) ⟨0, 0⟩
  intro ⟨F, n⟩
  refine ⟨⟨3 * n + 1 + F, n + 1⟩, ?_⟩
  show ⟨3 * n + 1 + F, 0, 0, 0, 3 * n⟩ [fm]⊢⁺
    ⟨3 * (n + 1) + 1 + (3 * n + 1 + F), 0, 0, 0, 3 * (n + 1)⟩
  rw [show 3 * (n + 1) + 1 + (3 * n + 1 + F) = 6 * n + 5 + F from by ring,
      show 3 * (n + 1) = 3 * n + 3 from by ring]
  exact main_trans F n

end Sz22_2003_unofficial_1843
