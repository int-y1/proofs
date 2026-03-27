import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #485: [28/15, 3/22, 175/2, 11/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  1  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_485

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: drain d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R3 repeated: drain a to c (b=0, e=0)
theorem r3_chain : ∀ k, ∀ a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R1/R2 interleave: k pairs
theorem r1r2_chain : ∀ k, ∀ i c d e, ⟨i, 1, c+k, d, e+k⟩ [fm]⊢* ⟨i+k, 1, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro i c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm  -- R1: (i+2, 0, c+k, d+1, e+k+1)
  rw [show i + 2 = (i + 1) + 1 from by ring,
      show e + k + 1 = (e + k) + 1 from by ring]
  step fm  -- R2: (i+1, 1, c+k, d+1, e+k)
  apply stepStar_trans (h (i+1) c (d+1) e); ring_nf; finish

-- R2 drain: works with any b, c=0
theorem r2_drain : ∀ k, ∀ a b d, ⟨a+k, b, 0, d, k⟩ [fm]⊢* ⟨a, b+k, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm  -- R2
  apply stepStar_trans (h a (b + 1) d); ring_nf; finish

-- Phase 5+6: from (a+1, b, 0, D, 0) to (0, 0, 2*a+2+3*b, D+a+1+3*b, 0)
theorem phase56 : ∀ b, ∀ a D, ⟨a+1, b, 0, D, 0⟩ [fm]⊢* ⟨0, 0, 2*a+2+3*b, D+a+1+3*b, 0⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a D
  rcases b with _ | _ | b
  · -- b=0: pure R3 chain
    rw [show a + 1 = 0 + (a + 1) from by ring]
    apply stepStar_trans (r3_chain (a+1) 0 0 D)
    ring_nf; finish
  · -- b=1: R3, R1, then R3 chain
    step fm  -- R3: (a, 1, 2, D+1, 0)
    step fm  -- R1: (a+2, 0, 1, D+2, 0)
    rw [show a + 2 = 0 + (a + 2) from by ring]
    apply stepStar_trans (r3_chain (a+2) 0 1 (D + 1 + 1))
    ring_nf; finish
  · -- b+2: R3, R1, R1, then recurse
    rw [show (b + 2 : ℕ) = (b + 1) + 1 from by ring]
    step fm  -- R3
    rw [show b + 1 + 1 = (b + 1 + 1 : ℕ) from by ring]
    step fm  -- R1
    rw [show (b + 1 + 1 : ℕ) = (b + 1) + 1 from by ring]
    step fm  -- R1
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih b (by omega) (a+3) (D + 1 + 1 + 1))
    ring_nf; finish

-- Main transition: parametrized by c and n where d = c + n, constraint n ≤ c
-- (0, 0, c+2, c+n+1, 0) ⊢⁺ (0, 0, 2*c+n+5, 2*c+2*n+5, 0)
theorem main_trans (c n : ℕ) (hnc : n ≤ c) :
    ⟨0, 0, c+2, c+n+1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2*c+n+5, 2*c+2*n+5, 0⟩ := by
  -- Phase 1: R4 transfer
  rw [show c + n + 1 = 0 + (c + n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (c+n+1) (c+2) 0 0)
  rw [show (0 : ℕ) + (c + n + 1) = c + n + 1 from by ring]
  -- Phase 2: R5
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm  -- R5: (0, 1, c+1, 0, c+n+1)
  -- Phase 3: R1/R2 interleave (c+1 pairs)
  rw [show c + 1 = 0 + (c + 1) from by ring,
      show c + n + 1 = n + (c + 1) from by ring]
  apply stepStar_trans (r1r2_chain (c+1) 0 0 0 n)
  -- After chain: (0+(c+1), 1, 0, 0+(c+1), n)
  -- Phase 4: R2 drain (n steps from e)
  rw [show (0 : ℕ) + (c + 1) = (c - n + 1) + n from by omega]
  apply stepStar_trans (r2_drain n (c-n+1) 1 ((c-n+1)+n))
  rw [show 1 + n = n + 1 from by ring,
      show c - n + 1 = (c - n) + 1 from by omega,
      show (c - n + 1) + n = c + 1 from by omega]
  -- Phase 5+6: from ((c-n)+1, n+1, 0, c+1, 0) to target
  apply stepStar_trans (phase56 (n+1) (c-n) (c+1))
  -- Goal: (0, 0, 2*(c-n)+2+3*(n+1), (c+1)+(c-n)+1+3*(n+1), 0) ⊢* target
  -- These are equal, but omega can't see through c-n.
  -- Use have to establish the equalities:
  have h1 : 2 * (c - n) + 2 + 3 * (n + 1) = 2 * c + n + 5 := by omega
  have h2 : c + 1 + (c - n) + 1 + 3 * (n + 1) = 2 * c + 2 * n + 5 := by omega
  rw [h1, h2]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c n, q = ⟨0, 0, c+2, c+n+1, 0⟩ ∧ n ≤ c)
  · intro q ⟨c, n, hq, hnc⟩
    subst hq
    refine ⟨⟨0, 0, 2*c+n+5, 2*c+2*n+5, 0⟩, ?_, main_trans c n hnc⟩
    refine ⟨2*c+n+3, n+1, ?_, by omega⟩
    have h1 : 2 * c + n + 5 = 2 * c + n + 3 + 2 := by omega
    have h2 : 2 * c + 2 * n + 5 = 2 * c + n + 3 + (n + 1) + 1 := by omega
    rw [h1, h2]
  · exact ⟨0, 0, rfl, Nat.zero_le _⟩

end Sz22_2003_unofficial_485
