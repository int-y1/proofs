import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1808: [9/10, 55/21, 2/3, 7/11, 189/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  3  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1808

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c, d+1, e⟩
  | _ => none

-- R2+R1 interleaving with b+1 to ensure b >= 1.
-- Each round: R2 then R1. Net effect: a-=1, b+=1, d-=1, e+=1.
-- (a+k+1, b+1, 0, d+k+1, e) →* (a+1, b+k+1, 0, d+1, e+k) then one more R2+R1.
-- Actually simpler: (a+k, b+1, 0, d+k, e) →* (a, b+k+1, 0, d, e+k)
theorem r2r1_chain : ∀ k, ∀ a b d e, ⟨a + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R2: (a+k+1, b, 1, d+k, e+1)
    step fm  -- R1: (a+k, b+2, 0, d+k, e+1)
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    ring_nf; finish

-- R3 repeated: drain b into a. (a, b+k, 0, 0, e) →* (a+k, b, 0, 0, e).
theorem r3_chain : ∀ k, ∀ a b e, ⟨a, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm  -- R3
    apply stepStar_trans (ih (a + 1) b e)
    ring_nf; finish

-- R4 repeated: drain e into d. (a, 0, 0, d, e+k) →* (a, 0, 0, d+k, e).
theorem r4_chain : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R4
    apply stepStar_trans (ih a (d + 1) e)
    ring_nf; finish

-- Main transition: (2n+3, 0, 0, n+1, 0) →⁺ (2n+5, 0, 0, n+2, 0)
theorem main_trans : ∀ n, ⟨2 * n + 3, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, n + 2, 0⟩ := by
  intro n
  -- R5: (2n+3, 0, 0, n+1, 0) → (2n+2, 3, 0, n+2, 0)
  step fm
  -- R2+R1 chain with k=n+1: (2n+2, 3, 0, n+2, 0) →* (n+1, n+4, 0, 1, n+1)
  rw [show (2 * n + 2 : ℕ) = (n + 1) + (n + 1) from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show (n + 2 : ℕ) = 1 + (n + 1) from by ring]
  apply stepStar_trans (r2r1_chain (n + 1) (n + 1) 2 1 0)
  rw [show 2 + (n + 1) + 1 = n + 4 from by ring,
      show 0 + (n + 1) = n + 1 from by ring]
  -- R2: (n+1, n+4, 0, 1, n+1) → (n+1, n+3, 1, 0, n+2)
  step fm
  -- R1: (n+1, n+3, 1, 0, n+2) → (n, n+5, 0, 0, n+2)
  step fm
  -- R3 chain: drain n+5 from b to a
  rw [show (n + 5 : ℕ) = 0 + (n + 5) from by ring]
  apply stepStar_trans (r3_chain (n + 5) n 0 (n + 2))
  rw [show n + (n + 5) = 2 * n + 5 from by ring]
  -- R4 chain: drain n+2 from e to d
  rw [show (n + 2 : ℕ) = 0 + (n + 2) from by ring]
  apply stepStar_trans (r4_chain (n + 2) (2 * n + 5) 0 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, n + 1, 0⟩) 0
  intro n; exists n + 1
  exact main_trans n
