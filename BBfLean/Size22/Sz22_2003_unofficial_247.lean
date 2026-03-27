import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #247: [135/2, 22/35, 1/5, 7/3, 1/77, 5/7]

Vector representation:
```
-1  3  1  0  0
 1  0 -1 -1  1
 0  0 -1  0  0
 0 -1  0  1  0
 0  0  0 -1 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_247

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R1+R2 chain: D pairs of (R1,R2).
-- (1, 3*k, 0, D, k+1) →* (1, 3*(k+D), 0, 0, k+D+1)
theorem r12_chain : ∀ D : ℕ, ∀ k : ℕ,
    ⟨1, 3*k, 0, D, k+1⟩ [fm]⊢* ⟨1, 3*(k+D), 0, 0, k+D+1⟩ := by
  intro D; induction' D with D ih <;> intro k
  · simp; finish
  · -- (1, 3*k, 0, D+1, k+1) → R1: (0, 3*k+3, 1, D+1, k+1) → R2: (1, 3*k+3, 0, D, k+2)
    step fm; step fm
    rw [show 3 * k + 3 = 3 * (k + 1) from by ring,
        show k + 1 + 1 = (k + 1) + 1 from by ring]
    apply stepStar_trans (ih (k + 1))
    ring_nf; finish

-- R4 chain: converts b to d. (0, b, 0, d, e) →* (0, 0, 0, d+b, e)
theorem b_to_d : ∀ b : ℕ, ∀ d e : ℕ, ⟨0, b, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d+b, e⟩ := by
  intro b; induction' b with b ih <;> intro d e
  · simp; finish
  · step fm
    apply stepStar_trans (ih (d+1) e)
    rw [show d + 1 + b = d + (b + 1) from by ring]; finish

-- R5 chain: cancel d and e. (0, 0, 0, d+e, e) →* (0, 0, 0, d, 0)
theorem de_cancel : ∀ e : ℕ, ∀ d : ℕ, ⟨0, 0, 0, d+e, e⟩ [fm]⊢* ⟨0, 0, 0, d, 0⟩ := by
  intro e; induction' e with e ih <;> intro d
  · simp; finish
  · rw [show d + (e + 1) = (d + e) + 1 from by ring]
    step fm
    exact ih d

-- Main transition: (0, 0, 0, D+2, 0) →⁺ (0, 0, 0, 2*D+2, 0)
theorem main_step (D : ℕ) : ⟨0, 0, 0, D+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*D+2, 0⟩ := by
  rw [show D + 2 = (D + 1) + 1 from by ring]
  -- R6: (0,0,1,D+1,0)
  step fm
  -- R2: (1,0,0,D,1) since d+1=D+1
  step fm
  -- R1: (0,3,1,D,1)
  step fm
  rcases D with _ | D
  · -- D = 0: (0, 3, 1, 0, 1)
    -- R3: (0, 3, 0, 0, 1)
    step fm
    apply stepStar_trans (b_to_d 3 0 1)
    simp
    exact de_cancel 1 2
  · -- D+1: (0, 3, 1, D+1, 1)
    -- R2: (1, 3, 0, D, 2)
    step fm
    rw [show (3 : ℕ) = 3 * 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (r12_chain D 1)
    -- At (1, 3*(1+D), 0, 0, 1+D+1) = (1, 3*D+3, 0, 0, D+2)
    -- R1: (0, 3*D+6, 1, 0, D+2)
    step fm
    rw [show 3 * (1 + D) + 3 = 3 * D + 6 from by ring,
        show 1 + D + 1 = D + 2 from by ring]
    -- R3: (0, 3*D+6, 0, 0, D+2)
    step fm
    apply stepStar_trans (b_to_d (3*D+6) 0 (D+2))
    simp
    rw [show 3 * D + 6 = (2 * D + 4) + (D + 2) from by ring]
    apply stepStar_trans (de_cancel (D+2) (2*D+4))
    rw [show 2 * D + 4 = 2 * (D + 1) + 2 from by ring]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩)
  · execute fm 5
  apply progress_nonhalt_simple (fm := fm) (C := fun n ↦ ⟨0, 0, 0, n + 3, 0⟩) (i₀ := 0)
  intro i
  refine ⟨2*i+1, ?_⟩
  rw [show i + 3 = (i + 1) + 2 from by ring,
      show 2 * i + 1 + 3 = 2 * (i + 1) + 2 from by ring]
  exact main_step (i + 1)

end Sz22_2003_unofficial_247
