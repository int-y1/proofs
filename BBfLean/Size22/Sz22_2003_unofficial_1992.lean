import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1992: [99/35, 5/6, 4/5, 7/11, 165/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  1  0  0
 2  0 -1  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1992

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

-- R1+R2 pairs: each pair does R1 then R2.
-- R1: (a, b, 1, d+1, e) -> (a, b+2, 0, d, e+1)
-- R2: (a+1, b+2, 0, d, e+1) -> (a, b+1, 1, d, e+1)
-- Net per pair: a-=1, b+=1, d-=1, e+=1, c stays at 1.
theorem r1r2_pairs : ∀ k, ∀ a b d e, ⟨a + k, b, 1, d + k, e⟩ [fm]⊢* ⟨a, b + k, 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R1: (a+k+1, b+2, 0, d+k, e+1)
    step fm  -- R2: (a+k, b+1, 1, d+k, e+1)
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    ring_nf; finish

-- R2 chain: drain a and b simultaneously, building c.
theorem r2_chain : ∀ k, ∀ a b c e, ⟨a + k, b + k, c, 0, e⟩ [fm]⊢* ⟨a, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring]
    step fm  -- R2
    apply stepStar_trans (ih a b (c + 1) e)
    ring_nf; finish

-- R3 chain: convert c to a (doubling).
theorem r3_chain : ∀ k, ∀ a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm  -- R3
    apply stepStar_trans (ih (a + 2) c e)
    ring_nf; finish

-- R4 chain: move e to d.
theorem r4_chain : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R4
    apply stepStar_trans (ih a (d + 1) e)
    ring_nf; finish

-- Main transition: (2n+3, 0, 0, n+1, 0) ⊢⁺ (2n+5, 0, 0, n+2, 0)
-- Phase 1: R5
-- Phase 2: R1+R2 pairs (n rounds) + final R1
-- Phase 3: R2 chain (n+2 times)
-- Phase 4: R3 (once) + R2 (once)
-- Phase 5: R3 chain (n+2 times)
-- Phase 6: R4 chain (n+2 times)
theorem main_trans : ∀ n, ⟨2 * n + 3, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, n + 2, 0⟩ := by
  intro n
  step fm
  rw [show 2 * n + 2 = (n + 2) + n from by ring,
      show n + 1 = 1 + n from by ring]
  apply stepStar_trans (r1r2_pairs n (n + 2) 1 1 1)
  step fm
  -- After R1: Lean has (n+2, 1+n+2, 0, 0, 1+n+1)
  -- Need to apply r2_chain: (a+k, b+k, c, 0, e) ⊢* (a, b, c+k, 0, e)
  -- So rewrite to (0+(n+2), 1+(n+2), 0, 0, 1+n+1)
  rw [show n + 2 = 0 + (n + 2) from by ring,
      show 1 + n + 2 = 1 + (n + 2) from by ring]
  apply stepStar_trans (r2_chain (n + 2) 0 1 0 (1 + n + 1))
  -- Now at (0, 1, 0+(n+2), 0, 1+n+1) = (0, 1, n+2, 0, n+2)
  rw [show (0 : ℕ) + (n + 2) = (n + 1) + 1 from by ring]
  step fm
  step fm
  -- After R3+R2: (1, 0, n+1+1, 0, 1+n+1)
  -- Need r3_chain: (a, 0, c+k, 0, e) ⊢* (a+2*k, 0, c, 0, e)
  rw [show n + 1 + 1 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r3_chain (n + 2) 1 0 (1 + n + 1))
  -- Now at (1+2*(n+2), 0, 0, 0, 1+n+1)
  -- Need r4_chain: (a, 0, 0, d, e+k) ⊢* (a, 0, 0, d+k, e)
  rw [show 1 + 2 * (n + 2) = 2 * n + 5 from by ring,
      show 1 + n + 1 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r4_chain (n + 2) (2 * n + 5) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, n + 1, 0⟩) 0
  intro n; exists n + 1; exact main_trans n
