import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #150: [1/45, 25/539, 98/5, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 0  0  2 -2 -1
 1  0 -1  2  0
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

The canonical states are (n²+3n+3, 0, 0, 4n+4, 0) for n ∈ ℕ.
The transition goes through four phases:
1. R4 chain: transfer d to b
2. R5+R1 drain: paired steps reducing b and a, increasing e
3. R5+R3 bridge then R2+R3 interleave: build up c while consuming e
4. R3 chain: transfer c to a and d

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_150

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- Phase 1: R4 chain, d → b
theorem d_to_b : ∀ k, ∀ a b d,
    ⟨a, b, 0, d + k, 0⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 2: R5+R1 drain, paired steps
theorem drain_b : ∀ k, ∀ a e,
    ⟨a + k, 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  step fm -- R5: (a+k, 2k+1+1, 1, 0, e+1)
  rw [show 2 * k + 1 + 1 = (2 * k) + 2 from by ring]
  step fm -- R1: (a+k, 2k, 0, 0, e+1)
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R2+R3 pair step
theorem r2r3_pair : ∀ a c e,
    ⟨a, 0, c, 2, e + 1⟩ [fm]⊢* ⟨a + 1, 0, c + 1, 2, e⟩ := by
  intro a c e
  step fm -- R2: (a, 0, c+2, 0, e)
  step fm -- R3: (a+1, 0, c+1, 2, e)
  finish

-- Phase 3a: R2+R3 interleave pairs
theorem interleave_pairs : ∀ k, ∀ a c e,
    ⟨a, 0, c, 2, e + k⟩ [fm]⊢* ⟨a + k, 0, c + k, 2, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  apply stepStar_trans (r2r3_pair _ _ _)
  rw [show c + 1 = (c + 1) from rfl]
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 4: R3 chain, c → a,d
theorem c_to_ad : ∀ k, ∀ a c d,
    ⟨a, 0, c + k, d, 0⟩ [fm]⊢* ⟨a + k, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm -- R3: (a+1, 0, c+k, d+2, 0)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: canonical state n to canonical state n+1
theorem main_trans : ∀ n,
    ⟨n^2 + 3*n + 3, 0, 0, 4*n + 4, 0⟩ [fm]⊢⁺
    ⟨(n+1)^2 + 3*(n+1) + 3, 0, 0, 4*(n+1) + 4, 0⟩ := by
  intro n
  -- Phase 1: R4 chain (first step gives stepPlus)
  rw [show 4 * n + 4 = 0 + (4 * n + 4) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨n^2 + 3*n + 3, 0, 0, 0 + (4*n + 4), 0⟩ =
         some ⟨n^2 + 3*n + 3, 1, 0, 0 + (4*n + 3), 0⟩
    simp [fm]
  apply stepStar_trans (d_to_b (4*n + 3) _ _ _)
  -- Now goal: (n²+3n+3, 1+(4n+3), 0, 0, 0) ⊢* target
  -- Phase 2: drain b
  show ⟨n^2 + 3*n + 3, 1 + (4*n + 3), 0, 0, 0⟩ [fm]⊢* _
  rw [show 1 + (4 * n + 3) = 2 * (2 * n + 2) from by ring,
      show n^2 + 3*n + 3 = (n^2 + n + 1) + (2*n + 2) from by ring]
  apply stepStar_trans (drain_b (2*n + 2) (n^2 + n + 1) 0)
  -- Bridge: R5 + R3
  step fm -- R5
  step fm -- R3
  -- Phase 3: interleave pairs
  show ⟨n^2 + n + 1, 0, 0, 2, 0 + (2 * n + 2) + 1⟩ [fm]⊢* _
  rw [show 0 + (2 * n + 2) + 1 = 1 + (2 * n + 2) from by ring]
  apply stepStar_trans (interleave_pairs (2*n + 2) (n^2 + n + 1) 0 1)
  show ⟨n^2 + n + 1 + (2*n + 2), 0, 0 + (2*n + 2), 2, 1⟩ [fm]⊢* _
  rw [show n^2 + n + 1 + (2 * n + 2) = n^2 + 3*n + 3 from by ring,
      show 0 + (2 * n + 2) = 2 * n + 2 from by ring]
  -- Final R2
  step fm
  -- Phase 4: R3 chain
  show ⟨n^2 + 3*n + 3, 0, 2*n + 2 + 2, 0, 0⟩ [fm]⊢* _
  rw [show 2 * n + 2 + 2 = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (c_to_ad (2*n + 4) (n^2 + 3*n + 3) 0 0)
  ring_nf; finish

-- Final theorem
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 4, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨n^2 + 3*n + 3, 0, 0, 4*n + 4, 0⟩)
  · intro q ⟨n, hq⟩
    subst hq
    refine ⟨⟨(n+1)^2 + 3*(n+1) + 3, 0, 0, 4*(n+1) + 4, 0⟩,
            ⟨n+1, rfl⟩, main_trans n⟩
  · exact ⟨0, by ring_nf⟩

end Sz22_2003_unofficial_150
