import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #159: [1/45, 385/2, 2/65, 507/7, 5/33]

Vector representation:
```
 0 -2 -1  0  0  0
-1  0  1  1  1  0
 1  0 -1  0  0 -1
 0  1  0 -1  0  2
 0 -1  1  0 -1  0
```

This Fractran program doesn't halt. The canonical states are `(0, 0, 0, 3*n+1, 5*n+3, 2)`.
Each cycle maps `(0, 0, 0, 3*n+1, 5*n+3, 2) →⁺ (0, 0, 0, 6*n+4, 10*n+8, 2)`, doubling the
parameter (successor function `f(n) = 2*n+1`).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_159

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+2⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- Phase 1: R4 drain. (0, b, 0, d+k, e, f) →* (0, b+k, 0, d, e, f+2*k)
theorem r4_drain : ∀ k b d e f,
    ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro b d e f; exists 0
  | succ k ih =>
    intro b d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- Phase 2: R5+R1 pairs. Each pair: b -= 3, e -= 1.
-- (0, 3*k+1, 0, 0, e+k, f) →* (0, 1, 0, 0, e, f)
theorem r5r1_drain : ∀ k e f,
    ⟨0, 3 * k + 1, 0, 0, e + k, f⟩ [fm]⊢* ⟨0, 1, 0, 0, e, f⟩ := by
  intro k; induction k with
  | zero => intro e f; exists 0
  | succ k ih =>
    intro e f
    rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 1 + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R5
    step fm  -- R1
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase 3: R2+R3 loop.
-- (1, 0, 0, d, e, f+k) →* (1, 0, 0, d+k, e+k, f)  when b=0
-- Actually need to be careful: R2 fires when a≥1, then R3 fires when c≥1 and f≥1.
-- (1, 0, 0, d, e, f+k):
--   R2: (0, 0, 1, d+1, e+1, f+k) -- then c=1, need f+k≥1... but we go through f+k-1, etc.
-- Wait, let me use the exact pattern from simulation.
-- Each R2+R3 pair: (1,0,0,d,e,f) → (0,0,1,d+1,e+1,f) → (1,0,0,d+1,e+1,f-1)
-- So after k pairs: (1,0,0,d+k,e+k,f-k) but only when f≥k.
-- Actually parameterize as (1,0,0,d,e,f+k) →* (1,0,0,d+k,e+k,f)
theorem r2r3_loop : ∀ k d e f,
    ⟨1, 0, 0, d, e, f + k⟩ [fm]⊢* ⟨1, 0, 0, d + k, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro d e f; exists 0
  | succ k ih =>
    intro d e f
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm  -- R2: (0, 0, 1, d+1, e+1, (f+k)+1)
    -- Wait, after R2 we have (0, 0, 1, d+1, e+1, f+k+1). But f+k+1 ≥ 1 so R3 fires.
    -- Actually R2 gives (0, 0, c+1, d+1, e+1, (f+k)+1) with c=0, so (0, 0, 1, d+1, e+1, (f+k)+1)
    -- Hmm, but then R3 needs c≥1 and f≥1, and we have c=1, f=f+k+1≥1. But wait:
    -- After R2 from (1, 0, 0, d, e, (f+k)+1): we get (0, 0, 1, d+1, e+1, (f+k)+1)
    -- R3: c≥1, f≥1 → (1, 0, 0, d+1, e+1, f+k)
    step fm  -- R3
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 3b: R2+R3 with b=1.
-- (1, 1, 0, d, e, f+k) →* (1, 1, 0, d+k, e+k, f)
-- But wait, when a=1 and b=1, R2 fires (a≥1): (0, 1, 1, d+1, e+1, f+k)
-- Then c=1, f+k≥1 (if k>0 or f>0) → R3: (1, 1, 0, d+1, e+1, f+k-1)
-- Same pattern, just b stays at 1.
theorem r2r3_loop_b1 : ∀ k d e f,
    ⟨1, 1, 0, d, e, f + k⟩ [fm]⊢* ⟨1, 1, 0, d + k, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro d e f; exists 0
  | succ k ih =>
    intro d e f
    rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm  -- R2
    step fm  -- R3
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Main transition: (0, 0, 0, 3*n+1, 5*n+3, 2) →⁺ (0, 0, 0, 6*n+4, 10*n+8, 2)
theorem main_trans : ∀ n,
    ⟨0, 0, 0, 3 * n + 1, 5 * n + 3, 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * n + 4, 10 * n + 8, 2⟩ := by
  intro n
  -- Phase 1: R4 drain (3n+1 steps)
  -- (0, 0, 0, 0+(3n+1), 5n+3, 2) →* (0, 3n+1, 0, 0, 5n+3, 2+2*(3n+1))
  --   = (0, 3n+1, 0, 0, 5n+3, 6n+4)
  rw [show 3 * n + 1 = 0 + (3 * n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact r4_drain (3 * n + 1) 0 0 (5 * n + 3) 2
  -- Now at (0, 3n+1, 0, 0, 5n+3, 6n+4)
  -- Phase 2: R5+R1 drain (n pairs)
  -- (0, 3n+1, 0, 0, (4n+3)+n, 6n+4) →* (0, 1, 0, 0, 4n+3, 6n+4)
  rw [show (0 : ℕ) + (3 * n + 1) = 3 * n + 1 from by ring,
      show 2 + 2 * (3 * n + 1) = 6 * n + 4 from by ring,
      show 5 * n + 3 = (4 * n + 3) + n from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact r5r1_drain n (4 * n + 3) (6 * n + 4)
  -- Now at (0, 1, 0, 0, 4n+3, 6n+4)
  -- R5: (0, 0, 1, 0, 4n+2, 6n+4)
  -- R3: (1, 0, 0, 0, 4n+2, 6n+3)
  rw [show (4 * n + 3 : ℕ) = (4 * n + 2) + 1 from by ring,
      show (6 * n + 4 : ℕ) = (6 * n + 3) + 1 from by ring]
  step fm  -- R5
  step fm  -- R3
  -- Now at (1, 0, 0, 0, 4n+2, 6n+3)
  -- Phase 3: R2+R3 loop (6n+3 iterations)
  -- (1, 0, 0, 0, 4n+2, 0+(6n+3)) →* (1, 0, 0, 6n+3, 4n+2+6n+3, 0)
  --   = (1, 0, 0, 6n+3, 10n+5, 0)
  rw [show 6 * n + 3 = 0 + (6 * n + 3) from by ring]
  apply stepStar_trans (r2r3_loop (6 * n + 3) 0 (4 * n + 2) 0)
  -- Now at (1, 0, 0, 6n+3, 10n+5, 0)
  -- R2: (0, 0, 1, 6n+4, 10n+6, 0)
  -- d≥1 so R4: wait, c=1 and f=0, R3 needs f≥1, doesn't fire.
  -- d=6n+4≥1 so R4: (0, 1, 1, 6n+3, 10n+6, 2)
  -- c=1, f=2≥1 so R3: (1, 1, 0, 6n+3, 10n+6, 1)
  -- R2: (0, 1, 1, 6n+4, 10n+7, 1)
  -- R3: (1, 1, 0, 6n+4, 10n+7, 0)
  -- R2: (0, 1, 1, 6n+5, 10n+8, 0)
  -- d≥1 so R4: (0, 2, 1, 6n+4, 10n+8, 2)
  -- R1: (0, 0, 0, 6n+4, 10n+8, 2) ✓
  step fm  -- R2
  step fm  -- R4
  step fm  -- R3
  step fm  -- R2
  step fm  -- R3
  step fm  -- R2
  step fm  -- R4
  step fm  -- R1
  ring_nf; finish

-- Bootstrap: c₀ →⁺ (0, 0, 0, 1, 3, 2) = C(0)
theorem bootstrap : c₀ [fm]⊢⁺ ⟨0, 0, 0, 1, 3, 2⟩ := by
  unfold c₀; execute fm 8

theorem nonhalt : ¬halts fm c₀ := by
  apply stepPlus_not_halts_not_halts bootstrap
  exact progress_nonhalt_simple (A := ℕ)
    (C := fun n ↦ (⟨0, 0, 0, 3 * n + 1, 5 * n + 3, 2⟩ : Q))
    (i₀ := 0)
    (fun n ↦ ⟨2 * n + 1, by
      have h := main_trans n
      rw [show 6 * n + 4 = 3 * (2 * n + 1) + 1 from by ring,
          show 10 * n + 8 = 5 * (2 * n + 1) + 3 from by ring] at h
      exact h⟩)

end Sz22_2003_unofficial_159
