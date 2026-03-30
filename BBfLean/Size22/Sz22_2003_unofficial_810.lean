import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #810: [35/6, 715/2, 8/77, 3/5, 2/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  1  0  1  1
 3  0  0 -1 -1  0
 0  1 -1  0  0  0
 1  0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_810

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- R4 chain: move c to b.
theorem c_to_b : ∀ k b c e f, ⟨0, b, c + k, 0, e, f⟩ [fm]⊢* ⟨0, b + k, c, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e f)
    ring_nf; finish

-- R3 + 3xR1 chain: k rounds.
-- (0, 3*k, c, d+1, e+k, f) ⊢* (0, 0, c+3*k, d+2*k+1, e, f)
theorem r3_r1_chain : ∀ k c d e f,
    ⟨0, 3 * k, c, d + 1, e + k, f⟩ [fm]⊢*
    ⟨0, 0, c + 3 * k, d + 2 * k + 1, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · simp; exists 0
  · -- Goal: (0, 3*(k+1), c, d+1, e+(k+1), f) ⊢* (0, 0, c+3*(k+1), d+2*(k+1)+1, e, f)
    -- Rewrite to get patterns right for step fm
    rw [show 3 * (k + 1) = 3 * k + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    -- Now: (0, 3*k+3, c, d+1, e+k+1, f) - R3 fires (d+1>=1, e+k+1>=1)
    step fm
    -- After R3: (3, 3*k+3, c, d, e+k, f) - but wait, a=3, b=3*k+3, so R1 fires
    step fm -- R1: (2, 3*k+2, c+1, d+1, e+k, f)
    step fm -- R1: (1, 3*k+1, c+2, d+2, e+k, f)
    step fm -- R1: (0, 3*k, c+3, d+3, e+k, f)
    -- Now: (0, 3*k, c+3, d+3, e+k, f)
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih (c + 3) (d + 2) e f)
    ring_nf; finish

-- R3 + 3xR2 chain: k rounds.
-- (0, 0, c, d+k, e+1, f) ⊢* (0, 0, c+3*k, d, e+2*k+1, f+3*k)
theorem r3_r2_chain : ∀ k c d e f,
    ⟨0, 0, c, d + k, e + 1, f⟩ [fm]⊢*
    ⟨0, 0, c + 3 * k, d, e + 2 * k + 1, f + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · simp; exists 0
  · rw [show d + (k + 1) = d + k + 1 from by ring]
    -- (0, 0, c, d+k+1, e+1, f) - R3 fires (d+k+1 >= 1, e+1 >= 1)
    step fm
    -- After R3: (3, 0, c, d+k, e, f) - R2 fires (a=3>=1, b=0)
    step fm -- R2: (2, 0, c+1, d+k, e+1, f+1)
    step fm -- R2: (1, 0, c+2, d+k, e+2, f+2)
    step fm -- R2: (0, 0, c+3, d+k, e+3, f+3)
    rw [show e + 3 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (c + 3) d (e + 2) (f + 3))
    ring_nf; finish

-- Main transition:
-- (0, 0, 3*k+1, 0, e+k+1, f+1) ⊢⁺ (0, 0, 9*k+4, 0, e+4*k+3, f+6*k+3)
theorem main_transition (k e f : ℕ) :
    ⟨0, 0, 3 * k + 1, 0, e + k + 1, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 9 * k + 4, 0, e + 4 * k + 3, f + 6 * k + 3⟩ := by
  -- Phase 1: c_to_b
  apply stepStar_stepPlus_stepPlus
  · rw [show 3 * k + 1 = 0 + (3 * k + 1) from by ring]
    exact c_to_b (3 * k + 1) 0 0 (e + k + 1) (f + 1)
  -- Now at (0, 3*k+1, 0, 0, e+k+1, f+1)
  rw [show (0 : ℕ) + (3 * k + 1) = 3 * k + 1 from by ring]
  -- Phase 2: R5 + R1
  step fm -- R5: (1, 3*k+1, 0, 0, e+k+1, f)
  rw [show 3 * k + 1 = (3 * k) + 1 from by ring]
  step fm -- R1: (0, 3*k, 1, 1, e+k+1, f)
  -- Phase 3: r3_r1_chain k rounds
  -- (0, 3*k, 1, 1, e+k+1, f) needs to match (0, 3*k, c, d+1, e'+k, f)
  -- with c=1, d=0, e'=e+1: d+1=1 ✓, e'+k = (e+1)+k = e+k+1 ✓
  rw [show e + k + 1 = (e + 1) + k from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3_r1_chain k 1 0 (e + 1) f)
  -- After phase 3: (0, 0, 1+3*k, 0+2*k+1, e+1, f)
  -- Phase 4: r3_r2_chain (2*k+1) rounds
  rw [show 1 + 3 * k = 3 * k + 1 from by ring,
      show 0 + 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_trans (r3_r2_chain (2 * k + 1) (3 * k + 1) 0 e f)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨k, e, f⟩ ↦ ⟨0, 0, 3 * k + 1, 0, e + k + 1, f + 1⟩) ⟨0, 0, 0⟩
  intro ⟨k, e, f⟩
  refine ⟨⟨3 * k + 1, e + k + 1, f + 6 * k + 2⟩, ?_⟩
  show ⟨0, 0, 3 * k + 1, 0, e + k + 1, f + 1⟩ [fm]⊢⁺
    ⟨0, 0, 3 * (3 * k + 1) + 1, 0, (e + k + 1) + (3 * k + 1) + 1, (f + 6 * k + 2) + 1⟩
  rw [show 3 * (3 * k + 1) + 1 = 9 * k + 4 from by ring,
      show (e + k + 1) + (3 * k + 1) + 1 = e + 4 * k + 3 from by ring,
      show (f + 6 * k + 2) + 1 = f + 6 * k + 3 from by ring]
  exact main_transition k e f

end Sz22_2003_unofficial_810
