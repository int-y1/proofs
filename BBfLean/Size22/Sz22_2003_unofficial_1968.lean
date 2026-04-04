import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1968: [99/35, 2/5, 25/6, 7/11, 165/2]

Vector representation:
```
 0  2 -1 -1  1
 1  0 -1  0  0
-1 -1  2  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1968

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

-- R4 chain: move e to d
theorem e_to_d : ∀ k, ∀ a d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm
    exact ih a (d + 1)

-- R3/R2/R2 drain: move b to a (requires a >= 1)
theorem r3r2r2_drain : ∀ k, ∀ a e, ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) e)
    ring_nf; finish

-- Combined unfolding + drain: from (F+D, B, 2, D, E) to (F+2D+B+2, 0, 0, 0, E+D)
theorem unfolding_drain : ∀ D, ∀ F B E,
    ⟨F + D, B, 2, D, E⟩ [fm]⊢* ⟨F + 2 * D + B + 2, 0, 0, 0, E + D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih
  intro F B E
  rcases D with _ | _ | D
  · -- D = 0: R2, R2, then drain
    step fm; step fm
    apply stepStar_trans (r3r2r2_drain B (F + 1) E)
    ring_nf; finish
  · -- D = 1: R1, R2, then drain
    step fm; step fm
    apply stepStar_trans (r3r2r2_drain (B + 2) (F + 1) (E + 1))
    ring_nf; finish
  · -- D + 2: R1, R1, R3, then IH with D
    rw [show F + (D + 2) = F + D + 2 from by ring]
    step fm; step fm; step fm
    rw [show F + D + 1 = (F + 1) + D from by ring]
    apply stepStar_trans (ih D (by omega) (F + 1) (B + 3) (E + 2))
    ring_nf; finish

-- Full transition: (F+n+2, 0, 0, n+1, 0) →⁺ (F+2n+4, 0, 0, n+2, 0)
theorem main_trans : ∀ n, ∀ F,
    ⟨F + n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨F + 2 * n + 4, 0, 0, n + 2, 0⟩ := by
  intro n F
  -- Opening: R5, R1, R3 (3 steps)
  rw [show F + n + 2 = (F + n + 1) + 1 from by ring]
  step fm  -- R5: (F+n+1, 1, 1, n+1, 1)
  step fm  -- R1: (F+n+1, 3, 0, n, 2)
  rw [show F + n + 1 = (F + n) + 1 from by ring]
  step fm  -- R3: (F+n, 2, 2, n, 2)
  -- Now apply unfolding_drain with A = F+n, B = 2, D = n, E = 2
  apply stepStar_trans (unfolding_drain n F 2 2)
  -- Result: (F + 2*n + 4, 0, 0, 0, 2 + n)
  show ⟨F + 2 * n + 2 + 2, 0, 0, 0, 2 + n⟩ [fm]⊢* ⟨F + 2 * n + 4, 0, 0, n + 2, 0⟩
  rw [show F + 2 * n + 2 + 2 = F + 2 * n + 4 from by ring,
      show (2 : ℕ) + n = n + 2 from by ring]
  have h := e_to_d (n + 2) (F + 2 * n + 4) 0
  simp at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, n⟩ ↦ ⟨F + n + 2, 0, 0, n + 1, 0⟩) ⟨0, 0⟩
  intro ⟨F, n⟩
  refine ⟨⟨F + n + 1, n + 1⟩, ?_⟩
  show ⟨F + n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨F + n + 1 + (n + 1) + 2, 0, 0, (n + 1) + 1, 0⟩
  rw [show F + n + 1 + (n + 1) + 2 = F + 2 * n + 4 from by ring,
      show (n + 1) + 1 = n + 2 from by ring]
  exact main_trans n F
