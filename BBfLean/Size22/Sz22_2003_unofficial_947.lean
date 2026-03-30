import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #947: [4/15, 33/14, 275/2, 7/11, 3/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_947

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) (e + 1)); ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, n + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * n + 5, 2 * n + 4, 0⟩ := by
  -- Phase A: R5, R1 opening (2 steps)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (n + 1) + 1, n + 1, 0⟩ = some ⟨0, 1, n + 1, n + 1, 0⟩
    unfold fm; simp only
  rw [show n + 1 = n + 1 from rfl]
  step fm
  -- State: (2, 0, n, n + 1, 0)
  -- Phase B: R2, R1 chain (n rounds)
  have hB := r2r1_chain n 1 0 1 0
  simp only [show 1 + 1 = 2 from rfl,
      show 1 + n = n + 1 from by ring,
      show 0 + n = n from by ring,
      show n + 1 + 1 = n + 2 from by ring] at hB
  apply stepStar_trans hB
  -- State: (n + 2, 0, 0, 1, n)
  -- Phase C: R2 (last d=1)
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  -- State: (n + 1, 1, 0, 0, n + 1)
  -- Phase D: R3
  step fm
  -- State: (n, 1, 2, 0, n + 2)
  -- Phase E: R1
  rw [show (1 : ℕ) = 0 + 1 from rfl,
      show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  -- State: (n + 2, 0, 1, 0, n + 2)
  -- Phase F: R3 drain
  apply stepStar_trans (r3_drain (n + 2) 1 (n + 2))
  rw [show 1 + 2 * (n + 2) = 2 * n + 5 from by ring,
      show n + 2 + (n + 2) = 2 * n + 4 from by ring]
  -- State: (0, 0, 2n+5, 0, 2n+4)
  -- Phase G: R4 drain
  have hG := r4_drain (2 * n + 4) (2 * n + 5) 0
  simp only [show 0 + (2 * n + 4) = 2 * n + 4 from by ring] at hG
  exact hG

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, n + 1, 0⟩) 0
  intro n
  refine ⟨2 * n + 3, ?_⟩
  show ⟨0, 0, n + 2, n + 1, 0⟩ [fm]⊢⁺ ⟨0, 0, (2 * n + 3) + 2, (2 * n + 3) + 1, 0⟩
  rw [show (2 * n + 3) + 2 = 2 * n + 5 from by ring,
      show (2 * n + 3) + 1 = 2 * n + 4 from by ring]
  exact main_trans n
