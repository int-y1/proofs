import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #309: [154/15, 1/3, 147/2, 5/539, 22/7]

Vector representation:
```
 1 -1 -1  1  1
 0 -1  0  0  0
-1  1  0  2  0
 0  0  1 -2 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_309

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 repeated k times: (0, 0, c, d+2*k, k) →* (0, 0, c+k, d, 0)
theorem r4_chain (d : ℕ) : ∀ k c, ⟨0, 0, c, d+2*k, k⟩ [fm]⊢* ⟨0, 0, c+k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro c; exists 0
  | succ k ih =>
    intro c
    have : d + 2 * (k + 1) = d + 2 * k + 2 := by ring
    rw [this]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- R1+R3 chain k times then R2: (0, 1, k, d, e) →* (0, 0, 0, d+3*k, e+k)
theorem r1r3_r2_chain : ∀ k d e, ⟨0, 1, k, d, e⟩ [fm]⊢* ⟨0, 0, 0, d+3*k, e+k⟩ := by
  intro k; induction k with
  | zero =>
    intro d e
    step fm; finish
  | succ k ih =>
    intro d e
    step fm; step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Main transition: (0, 0, 0, D+2*n+1, n) →⁺ (0, 0, 0, D+3*n+2, n+1)
theorem main_trans (D n : ℕ) :
    ⟨0, 0, 0, D+2*n+1, n⟩ [fm]⊢⁺ ⟨0, 0, 0, D+3*n+2, n+1⟩ := by
  rw [show D + 2 * n + 1 = (D + 1) + 2 * n from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (D + 1) n 0)
  simp only [Nat.zero_add]
  step fm; step fm
  apply stepStar_trans (r1r3_r2_chain n (D + 2) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D n, q = ⟨0, 0, 0, D + 2 * n + 1, n⟩ ∧ D + n ≥ 1)
  · intro c ⟨D, n, hq, hDn⟩
    subst hq
    refine ⟨⟨0, 0, 0, D + 3 * n + 2, n + 1⟩,
            ⟨D + n - 1, n + 1, ?_, by omega⟩,
            main_trans D n⟩
    show (0, 0, 0, D + 3 * n + 2, n + 1) = (0, 0, 0, D + n - 1 + 2 * (n + 1) + 1, n + 1)
    have : D + n - 1 + 2 * (n + 1) + 1 = D + 3 * n + 2 := by omega
    rw [this]
  · exact ⟨1, 0, rfl, by omega⟩
