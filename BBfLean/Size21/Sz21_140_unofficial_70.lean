import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #70: [4/15, 33/14, 5/2, 7/11, 44/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  1  0  0
 0  0  0  1 -1
 2  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_70

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | _ => none

-- Phase 1: R3 repeated: a → c (when b=0, d=0)
-- (a+k, 0, c, 0, e) →* (a, 0, c+k, 0, e)
theorem a_to_c : ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  have many_step : ∀ k a c, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
    intro k; induction' k with k h <;> intro a c
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a c

-- Phase 2: R4 repeated: e → d
-- (0, 0, c, d, e+k) →* (0, 0, c, d+k, e)
theorem e_to_d : ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  have many_step : ∀ k d e, ⟨0, 0, c, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k d e

-- Phase 4: R2-R1 chain, drain j pairs
-- State after k pairs: (2+k, 0, n-k, n-k, 1+k)
-- Prove: (2+k, 0, j, j, 1+k) →* (2+k+j, 0, 0, 0, 1+k+j) by induction on j
theorem r2r1_drain : ∀ j, ∀ k, ⟨2+k, 0, j, j, 1+k⟩ [fm]⊢* ⟨2+k+j, 0, 0, 0, 1+k+j⟩ := by
  intro j; induction' j with j h <;> intro k
  · exists 0
  -- State: (2+k, 0, j+1, j+1, 1+k)
  -- Rewrite to expose R2 pattern: ((1+k)+1, 0, j+1, j+1, 1+k)
  rw [show 2 + k = (1 + k) + 1 from by ring]
  -- R2: a+1=(1+k)+1, d+1=j+1 → (1+k, 1, j+1, j, (1+k)+1)
  step fm
  -- State: (1+k, 1, j+1, j, (1+k)+1)
  -- R1: b+1=1+1=2? No, b=1 means b+1=2. Actually R1 pattern is (a, b+1, c+1, d, e)
  -- So b≥1 and c≥1: b=1≥1, c=j+1≥1 → R1 fires
  step fm
  -- State: ((1+k)+2, 0, j, j, (1+k)+1) = (3+k, 0, j, j, 2+k)
  -- = (2+(k+1), 0, j, j, 1+(k+1))
  rw [show 1 + k + 1 + (j + 1) = 2 + (k + 1) + j from by ring,
      show 1 + k + (j + 1) = 1 + (k + 1) + j from by ring,
      show (1 + k + 2 : ℕ) = 2 + (k + 1) from by ring,
      show (1 + k + 1 : ℕ) = 1 + (k + 1) from by ring]
  exact h (k + 1)

-- Main transition: (n+1, 0, 0, 0, n) →⁺ (n+2, 0, 0, 0, n+1)
theorem main_trans : ⟨n+1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, n+1⟩ := by
  -- Phase 1: R3 repeated (n+1) times: (n+1, 0, 0, 0, n) →* (0, 0, n+1, 0, n)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, 0, n⟩)
  · have h := @a_to_c 0 (n+1) 0 n
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 repeated n times: (0, 0, n+1, 0, n) →* (0, 0, n+1, n, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, n, 0⟩)
  · have h := @e_to_d (n+1) 0 0 n
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 once: (0, 0, n+1, n, 0) → (2, 0, n, n, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨2, 0, n, n, 1⟩)
  · show fm ⟨0, 0, n + 1, n, 0⟩ = some ⟨2, 0, n, n, 1⟩; simp [fm]
  -- Phase 4: R2-R1 chain n times: (2, 0, n, n, 1) →* (n+2, 0, 0, 0, n+1)
  have h := @r2r1_drain n 0
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 0, n⟩) 1
  intro n; exact ⟨n+1, main_trans⟩
