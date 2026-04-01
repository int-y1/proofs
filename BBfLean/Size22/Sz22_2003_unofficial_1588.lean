import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1588: [70/3, 3/55, 1/5, 1331/2, 1/77, 5/11]

Vector representation:
```
 1 -1  1  1  0
 0  1 -1  0 -1
 0  0 -1  0  0
-1  0  0  0  3
 0  0  0 -1 -1
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1588

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d, e+3*k)
theorem r4_chain : ∀ k a e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 3 * k⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e
    rw [Nat.add_succ a k]
    step fm
    apply stepStar_trans (ih a (e + 3))
    rw [show e + 3 + 3 * k = e + 3 * (k + 1) from by ring]
    finish

-- R5 chain: (0, 0, 0, d+k, e+k) →* (0, 0, 0, d, e)
theorem r5_chain : ∀ k d e, ⟨0, 0, 0, d + k, e + k⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e
    rw [Nat.add_succ d k, Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih d e)
    finish

-- R1+R2 interleave: (a, 0, 1, d, k) →* (a+k, 0, 1, d+k, 0)
theorem r1r2_chain : ∀ k a d, ⟨a, 0, 1, d, k⟩ [fm]⊢* ⟨a + k, 0, 1, d + k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a d; exists 0
  · intro a d
    step fm  -- R2: (a, 1, 0, d, k)
    step fm  -- R1: (a+1, 0, 1, d+1, k)
    apply stepStar_trans (ih (a + 1) (d + 1))
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show d + 1 + k = d + (k + 1) from by ring]
    finish

-- (n+2, 0, 0, n+2, 0) →* (0, 0, 0, 0, 2*n+4)
theorem phase_r4_r5 : ⟨n + 2, 0, 0, n + 2, 0⟩ [fm]⊢* ⟨0, 0, 0, 0, 2 * n + 4⟩ := by
  have h1 := r4_chain (n + 2) 0 0 (d := n + 2)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  have h2 := r5_chain (n + 2) 0 (2 * n + 4)
  simp only [Nat.zero_add] at h2
  rw [show 3 * (n + 2) = (2 * n + 4) + (n + 2) from by ring]
  exact h2

-- (0, 0, 0, 0, 2*n+4) →⁺ (2*n+3, 0, 0, 2*n+3, 0)
theorem phase_tail : ⟨0, 0, 0, 0, 2 * n + 4⟩ [fm]⊢⁺ ⟨2 * n + 3, 0, 0, 2 * n + 3, 0⟩ := by
  rw [show 2 * n + 4 = (2 * n + 3) + 1 from by omega]
  step fm  -- R6: (0, 0, 1, 0, 2n+3)
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by omega]
  step fm  -- R2: (0, 1, 0, 0, 2n+2)
  step fm  -- R1: (1, 0, 1, 1, 2n+2)
  apply stepStar_trans (r1r2_chain (2 * n + 2) 1 1)
  rw [show 1 + (2 * n + 2) = 2 * n + 3 from by ring]
  step fm; finish  -- R3

-- Main transition
theorem main_trans : ⟨n + 2, 0, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨2 * n + 3, 0, 0, 2 * n + 3, 0⟩ :=
  stepStar_stepPlus_stepPlus phase_r4_r5 phase_tail

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 2, 0⟩) 0
  intro n; exact ⟨2 * n + 1, main_trans⟩
