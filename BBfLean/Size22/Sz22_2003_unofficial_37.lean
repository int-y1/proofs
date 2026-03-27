import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #37: [1/15, 343/3, 6/77, 5/49, 363/2]

Vector representation:
```
 0 -1 -1  0  0
 0 -1  0  3  0
 1  1  0 -1 -1
 0  0  1 -2  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_37

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3 chain: (a, 0, c, d+2k, 0) →* (a, 0, c+k, d, 0)
theorem r3_chain : ⟨a, 0, c, d + 2 * k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  have h : ∀ k c, ⟨a, 0, c, d + 2 * k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
    intro k; induction' k with k ih <;> intro c
    · exists 0
    rw [Nat.mul_succ, ← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish
  exact h k c

-- Opening 4 steps: (n+1, 0, n+2, 1, 0) → (n+1, 0, n, 0, 1)
theorem opening_steps : ⟨n + 1, 0, n + 2, 1, 0⟩ [fm]⊢* ⟨n + 1, 0, n, 0, 1⟩ := by
  execute fm 4

-- R4/R0 drain: (k+1, 0, k, 0, e) →* (1, 0, 0, 0, e+2k)
theorem r4r0_drain : ⟨k + 1, 0, k, 0, e⟩ [fm]⊢* ⟨1, 0, 0, 0, e + 2 * k⟩ := by
  have h : ∀ k e, ⟨k + 1, 0, k, 0, e⟩ [fm]⊢* ⟨1, 0, 0, 0, e + 2 * k⟩ := by
    intro k; induction' k with k ih <;> intro e
    · exists 0
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih _)
    ring_nf; finish
  exact h k e

-- R4/R1: (1, 0, 0, 0, e) → (0, 0, 0, 3, e+2)
theorem r4_r1 : ⟨1, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 3, e + 2⟩ := by
  execute fm 2

-- R2/R1 chain: (a, 0, 0, d+1, k+1) →* (a+k+1, 0, 0, d+2k+3, 0)
theorem r2r1_chain : ⟨a, 0, 0, d + 1, k + 1⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + 2 * k + 3, 0⟩ := by
  have h : ∀ k a d, ⟨a, 0, 0, d + 1, k + 1⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d + 2 * k + 3, 0⟩ := by
    intro k; induction' k with k ih <;> intro a d
    · step fm; step fm; ring_nf; finish
    rw [show (k + 1) + 1 = k + 1 + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h k a d

-- Main transition: (n+2, 0, 0, 2n+7, 0) →⁺ (2n+5, 0, 0, 4n+13, 0)
theorem main_trans (n : ℕ) :
    (⟨n + 2, 0, 0, 2 * n + 7, 0⟩ : Q) [fm]⊢⁺ ⟨2 * n + 5, 0, 0, 4 * n + 13, 0⟩ := by
  -- Take one R3 step to get ⊢⁺
  rw [show 2 * n + 7 = (2 * n + 5) + 2 from by omega]
  apply step_stepStar_stepPlus (by unfold fm; rfl : (⟨n + 2, 0, 0, (2 * n + 5) + 2, 0⟩ : Q) [fm]⊢ ⟨n + 2, 0, 1, 2 * n + 5, 0⟩)
  rw [show 2 * n + 5 = 1 + 2 * (n + 2) from by omega]
  apply stepStar_trans r3_chain
  rw [show 1 + (n + 2) = n + 3 from by omega]
  rw [show n + 2 = (n + 1) + 1 from by omega, show n + 3 = (n + 1) + 2 from by omega]
  apply stepStar_trans opening_steps
  apply stepStar_trans r4r0_drain
  rw [show 1 + 2 * (n + 1) = 2 * n + 3 from by omega]
  apply stepStar_trans r4_r1
  rw [show (3 : ℕ) = 2 + 1 from by omega, show 2 * n + 5 = (2 * n + 4) + 1 from by omega]
  apply stepStar_trans (r2r1_chain (a := 0) (d := 2) (k := 2 * n + 4))
  ring_nf; finish

theorem main_trans' (n : ℕ) :
    (⟨n + 2, 0, 0, 2 * n + 7, 0⟩ : Q) [fm]⊢⁺ ⟨(2 * n + 3) + 2, 0, 0, 2 * (2 * n + 3) + 7, 0⟩ := by
  have h := main_trans n
  rw [show 2 * n + 5 = (2 * n + 3) + 2 from by omega,
      show 4 * n + 13 = 2 * (2 * n + 3) + 7 from by omega] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 7, 0⟩)
  · execute fm 6
  · show ¬halts fm (⟨2, 0, 0, 7, 0⟩ : Q)
    rw [show (⟨2, 0, 0, 7, 0⟩ : Q) = (⟨0 + 2, 0, 0, 2 * 0 + 7, 0⟩ : Q) from rfl]
    apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n ↦ ⟨n + 2, 0, 0, 2 * n + 7, 0⟩) 0
    intro n; exact ⟨2 * n + 3, main_trans' n⟩

end Sz22_2003_unofficial_37
