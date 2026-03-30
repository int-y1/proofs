import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #899: [4/15, 3/14, 275/2, 1/3, 7/11, 3/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  2  0  1
 0 -1  0  0  0
 0  0  0  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_899

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 chain: (a+k, 0, c, 0, e) →* (a, 0, c+2*k, 0, e+k)
-- R3 fires: a≥1, b=0, d=0 (R1 needs b≥1, R2 needs d≥1)
theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) (e + 1))
    ring_nf; finish

-- R5 chain: (0, 0, c, d, e+k) →* (0, 0, c, d+k, e)
-- R5 fires: a=0, b=0 (R1-R4 don't fire), e≥1
theorem r5_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e)
    ring_nf; finish

-- R1R2 interleave: ∀ d, (a, 0+1, c+d, d, 0) →* (a+d, 0+1, c, 0, 0)
-- Each round: R1 fires (b≥1, c≥1), then R2 fires (a≥1, d≥1)
theorem r1r2_chain : ∀ d, ∀ a c, ⟨a, 0 + 1, c + d, d, 0⟩ [fm]⊢* ⟨a + d, 0 + 1, c, 0, 0⟩ := by
  intro d; induction' d with d ih <;> intro a c
  · exists 0
  · rw [show c + (d + 1) = (c + d) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) c)
    ring_nf; finish

-- R6+R1R2+R1: (0, 0, C+D+2, D+1, 0) →⁺ (D+3, 0, C, 0, 0)
-- R6: (0, 0, (C+D+1)+1, D+1, 0) → (0, 1, C+D+1, D+1, 0)
-- R1R2 (D+1 rounds): (0, 1, C+D+1, D+1, 0) →* (D+1, 1, C, 0, 0)
-- R1: (D+1, 0+1, C+1-1, 0, 0) ... hmm, need C ≥ 0 for the last R1.
-- Actually: (D+1, 1, C, 0, 0) only fires R1 if C ≥ 1 (needs b≥1 and c≥1).
-- If C = 0: R4 fires (b≥1): (D+1, 0, 0, 0, 0). Not what we want.
-- So we need C ≥ 1.
-- R1: (D+1, 0+1, (C-1)+1, 0, 0) → (D+3, 0, C-1, 0, 0)
-- So: (0, 0, C+D+2, D+1, 0) →⁺ (D+3, 0, C-1, 0, 0) when C ≥ 1

-- Let me parameterize as: (0, 0, c+d+3, d+1, 0) →⁺ (d+3, 0, c, 0, 0)
-- Check: C+D+2 = c+d+3, so c = C-1, and we output (D+3, 0, C-1, 0, 0) = (d+3, 0, c, 0, 0). ✓
theorem r6_r1r2_r1 : ∀ d, ∀ c, ⟨0, 0, c + d + 3, d + 1, 0⟩ [fm]⊢⁺ ⟨d + 3, 0, c, 0, 0⟩ := by
  intro d c
  -- R6: (0, 0, (c+d+2)+1, (d+0)+1, 0) → (0, 0+1, c+d+2, (d+0)+1, 0)
  rw [show c + d + 3 = (c + d + 2) + 1 from by ring]
  step fm
  -- R1R2 chain: (0, 0+1, (c+1)+(d+1), d+1, 0) →* ((d+1), 0+1, c+1, 0, 0)
  apply stepStar_trans
  · rw [show c + d + 2 = (c + 1) + (d + 1) from by ring,
        show d + 1 = d + 1 from rfl]
    exact r1r2_chain (d + 1) 0 (c + 1)
  -- Final R1: (d+1, 0+1, (c)+1, 0, 0) → (d+3, 0, c, 0, 0)
  rw [show 0 + (d + 1) = d + 1 from by ring,
      show c + 1 = c + 1 from rfl]
  step fm
  ring_nf; finish

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨2 * n + 5, 0, n * (n + 2), 0, 0⟩ [fm]⊢⁺ ⟨2 * (n + 1) + 5, 0, (n + 1) * ((n + 1) + 2), 0, 0⟩ := by
  rcases n with _ | n
  · -- n=0: (5,0,0,0,0) →⁺ (7,0,3,0,0)
    execute fm 22
  · -- n≥1: n+1 = n'+2 where n' = n
    -- (2(n+1)+5, 0, (n+1)*(n+3), 0, 0)
    -- Phase 1: R3 chain
    apply stepStar_stepPlus_stepPlus
    · rw [show 2 * (n + 1) + 5 = 0 + (2 * n + 7) from by ring]
      exact r3_chain (2 * n + 7) 0 ((n + 1) * (n + 1 + 2)) 0
    -- State: (0, 0, (n+1)*(n+3) + 2*(2n+7), 0, 2n+7)
    -- Phase 2: R5 chain
    apply stepStar_stepPlus_stepPlus
    · rw [show (0 : ℕ) + (2 * n + 7) = 0 + (2 * n + 7) from rfl]
      exact r5_chain (2 * n + 7) ((n + 1) * (n + 1 + 2) + 2 * (2 * n + 7)) 0 0
    -- State: (0, 0, (n+1)*(n+3)+2*(2n+7), 2n+7, 0)
    -- Phase 3: R6 + R1R2 + R1
    -- Need: (n+1)*(n+3)+2*(2n+7) = c + d + 3 where d+1 = 2n+7 i.e. d = 2n+6
    -- (n+1)*(n+3)+2*(2n+7) = n²+4n+3+4n+14 = n²+8n+17
    -- c + d + 3 = c + 2n+6 + 3 = c + 2n+9
    -- so c = n²+8n+17 - 2n-9 = n²+6n+8
    -- output: (d+3, 0, c, 0, 0) = (2n+9, 0, n²+6n+8, 0, 0)
    -- = (2(n+2)+5, 0, (n+2)*(n+4), 0, 0). Check: (n+2)*(n+4) = n²+6n+8 ✓
    rw [show 0 + (2 * n + 7) = (2 * n + 6) + 1 from by ring,
        show (n + 1) * (n + 1 + 2) + 2 * (2 * n + 7) = (n * n + 6 * n + 8) + (2 * n + 6) + 3 from by ring]
    apply stepPlus_stepStar_stepPlus (r6_r1r2_r1 (2 * n + 6) (n * n + 6 * n + 8))
    rw [show 2 * n + 6 + 3 = 2 * (n + 1 + 1) + 5 from by ring,
        show n * n + 6 * n + 8 = (n + 1 + 1) * ((n + 1 + 1) + 2) from by ring]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 0⟩) (by execute fm 20)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 5, 0, n * (n + 2), 0, 0⟩) 0
  intro n; exists (n + 1)
  exact main_trans n
