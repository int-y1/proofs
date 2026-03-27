import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #153: [1/45, 2695/2, 2/65, 39/7, 5/33]

Vector representation:
```
 0 -2 -1  0  0  0
-1  0  1  2  1  0
 1  0 -1  0  0 -1
 0  1  0 -1  0  1
 0 -1  1  0 -1  0
```

This Fractran program doesn't halt. The canonical states are `(0, 0, 0, 3*n-1, 2*n, 1)`.
Each cycle maps `(0, 0, 0, 3*n-1, 2*n, 1) →⁺ (0, 0, 0, 6*n-1, 4*n, 1)`, doubling n.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_153

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+2, e+1, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- Phase 1: R4 drain. Transfer d to b and f.
-- (a, b, 0, d+k, e, f) →* (a, b+k, 0, d, e, f+k) when a=0, c=0.
-- But we need a=0 to avoid R2 firing. Let's just match the exact shape.
theorem r4_drain : ∀ k b d e f,
    ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f + k⟩ := by
  intro k; induction k with
  | zero => intro b d e f; exists 0
  | succ k ih =>
    intro b d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Phase 2: R5+R1 pairs. Each pair: b -= 3, e -= 1.
-- (0, 3*k+2, 0, 0, e+k, f) →* (0, 2, 0, 0, e, f) when a=0, c=0, d=0
theorem r5r1_drain : ∀ k e f,
    ⟨0, 3 * k + 2, 0, 0, e + k, f⟩ [fm]⊢* ⟨0, 2, 0, 0, e, f⟩ := by
  intro k; induction k with
  | zero => intro e f; exists 0
  | succ k ih =>
    intro e f
    rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 1 + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R5: b-1, c+1, e-1
    step fm  -- R1: b-2, c-1
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase 3: R2+R3 loop.
-- (1, 1, 0, d, e, f+k) →* (1, 1, 0, d+2*k, e+k, f)
theorem r2r3_loop : ∀ k d e f,
    ⟨1, 1, 0, d, e, f + k⟩ [fm]⊢* ⟨1, 1, 0, d + 2 * k, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro d e f; exists 0
  | succ k ih =>
    intro d e f
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm  -- R2: a-1, c+1, d+2, e+1
    step fm  -- R3: a+1, c-1, f-1
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition: (0, 0, 0, 3*(n+1)-1, 2*(n+1), 1) →⁺ (0, 0, 0, 6*(n+1)-1, 4*(n+1), 1)
theorem main_trans : ∀ n,
    ⟨0, 0, 0, 3 * n + 2, 2 * n + 2, 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * n + 5, 4 * n + 4, 1⟩ := by
  intro n
  -- Phase 1: R4 drain (3n+2 steps)
  -- (0, 0, 0, 0+(3n+2), 2n+2, 1) →* (0, 3n+2, 0, 0, 2n+2, 1+(3n+2))
  rw [show 3 * n + 2 = 0 + (3 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact r4_drain (3 * n + 2) 0 0 (2 * n + 2) 1
  -- Now at (0, 3n+2, 0, 0, 2n+2, 3n+3)
  -- Phase 2: R5+R1 drain (n pairs)
  -- (0, 3n+2, 0, 0, (n+2)+n, 3n+3) →* (0, 2, 0, 0, n+2, 3n+3)
  rw [show (0 : ℕ) + (3 * n + 2) = 3 * n + 2 from by ring,
      show 1 + (3 * n + 2) = 3 * n + 3 from by ring,
      show 2 * n + 2 = (n + 2) + n from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact r5r1_drain n (n + 2) (3 * n + 3)
  -- Now at (0, 2, 0, 0, n+2, 3n+3)
  -- Phase 3: R5 then R3 (2 steps)
  -- (0, 2, 0, 0, n+2, 3n+3) → (0, 1, 1, 0, n+1, 3n+3) → (1, 1, 0, 0, n+1, 3n+2)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show n + 2 = (n + 1) + 1 from by ring,
      show 3 * n + 3 = (3 * n + 2) + 1 from by ring]
  step fm  -- R5
  step fm  -- R3
  -- Now at (1, 1, 0, 0, n+1, 3n+2)
  -- Phase 4: R2+R3 loop (3n+2 pairs)
  -- (1, 1, 0, 0, n+1, 0+(3n+2)) →* (1, 1, 0, 6n+4, 4n+3, 0)
  rw [show 3 * n + 2 = 0 + (3 * n + 2) from by ring]
  apply stepStar_trans (r2r3_loop (3 * n + 2) 0 (n + 1) 0)
  -- Now at (1, 1, 0, 0+2*(3n+2), (n+1)+(3n+2), 0) = (1, 1, 0, 6n+4, 4n+3, 0)
  -- Phase 5: R2 then R4 then R1
  -- R2: (0, 1, 1, 6n+6, 4n+4, 0)
  -- R4: (0, 2, 1, 6n+5, 4n+4, 1)
  -- R1: (0, 0, 0, 6n+5, 4n+4, 1)
  step fm  -- R2
  step fm  -- R4
  step fm  -- R1
  ring_nf; finish

-- Bootstrap: c₀ →⁺ (0, 0, 0, 2, 2, 1)
theorem bootstrap : c₀ [fm]⊢⁺ ⟨0, 0, 0, 2, 2, 1⟩ := by
  unfold c₀; execute fm 6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepPlus_not_halts_not_halts bootstrap
  -- C(n) = (0, 0, 0, 3*(n+1)-1, 2*(n+1), 1) = (0, 0, 0, 3n+2, 2n+2, 1)
  -- C(0) = (0, 0, 0, 2, 2, 1) ✓
  -- main_trans n shows C(n) ⊢⁺ (0, 0, 0, 6n+5, 4n+4, 1)
  -- We need i' such that C(i') = (0, 0, 0, 6n+5, 4n+4, 1)
  -- C(i') = (0, 0, 0, 3i'+2, 2i'+2, 1), so 3i'+2 = 6n+5, i' = 2n+1
  exact progress_nonhalt_simple (A := ℕ)
    (C := fun n ↦ (⟨0, 0, 0, 3 * n + 2, 2 * n + 2, 1⟩ : Q))
    (i₀ := 0)
    (fun n ↦ ⟨2 * n + 1, by
      have h := main_trans n
      rw [show 6 * n + 5 = 3 * (2 * n + 1) + 2 from by ring,
          show 4 * n + 4 = 2 * (2 * n + 1) + 2 from by ring] at h
      exact h⟩)

end Sz22_2003_unofficial_153
