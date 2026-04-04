import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1801: [9/10, 539/2, 4/21, 5/7, 14/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  2  1
 2 -1  0 -1  0
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1801

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase 1: R4 chain. Move d to c.
theorem d_to_c : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- Phase 2 block: 5 steps consuming 3 from c and 1 from e, producing 5 in b.
theorem phase2_block : ⟨0, b, c + 3, 0, e + 1⟩ [fm]⊢* ⟨0, b + 5, c, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Phase 2 loop: k iterations of the 5-step block.
theorem phase2_loop : ∀ k, ⟨0, b, 3 * k + 2, 0, f + k + 1⟩ [fm]⊢* ⟨0, b + 5 * k, 2, 0, f + 1⟩ := by
  intro k; induction' k with k ih generalizing b f
  · exists 0
  · rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 3 from by ring,
        show f + (k + 1) + 1 = (f + k + 1) + 1 from by ring]
    rw [show (3 * k + 2) + 3 = (3 * k + 2) + 3 from rfl]
    apply stepStar_trans phase2_block
    apply stepStar_trans (ih (b := b + 5) (f := f))
    ring_nf; finish

-- Phase 2 remainder: handle the c=2 case.
theorem phase2_remainder : ⟨0, b, 2, 0, e + 1⟩ [fm]⊢⁺ ⟨0, b + 3, 0, 2, e + 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Phase 3: R3+R2+R2 drain. Each cycle: b decreases by 1, d increases by 3, e increases by 2.
theorem phase3 : ∀ B, ⟨0, B, 0, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 1 + 3 * B, e + 2 * B⟩ := by
  intro B; induction' B with B ih generalizing d e
  · exists 0
  · step fm; step fm; step fm
    rw [show d + 2 + 2 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d := d + 3) (e := e + 2))
    ring_nf; finish

-- Main transition: from canonical state to next canonical state.
theorem main_trans (n F : ℕ) : ⟨0, 0, 0, 3 * n + 2, F + n + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * (5 * n + 3) + 2, (5 * n + F + 3) + (5 * n + 3) + 1⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show (3 * n + 2 : ℕ) = 0 + (3 * n + 2) from by ring]
    apply stepStar_trans (d_to_c (3 * n + 2) (c := 0) (d := 0) (e := F + n + 1))
    simp
    exact phase2_loop n (b := 0) (f := F)
  · apply stepPlus_stepStar_stepPlus phase2_remainder
    rw [show 0 + 5 * n + 3 = 5 * n + 3 from by ring]
    show ⟨0, 5 * n + 3, 0, 2, F + 1⟩ [fm]⊢* ⟨0, 0, 0, 3 * (5 * n + 3) + 2, (5 * n + F + 3) + (5 * n + 3) + 1⟩
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (phase3 (5 * n + 3) (d := 1) (e := F + 1))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3 * 0 + 2, 0 + 0 + 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, F⟩ ↦ ⟨0, 0, 0, 3 * n + 2, F + n + 1⟩) ⟨0, 0⟩
  intro ⟨n, F⟩
  exact ⟨⟨5 * n + 3, 5 * n + F + 3⟩, main_trans n F⟩
