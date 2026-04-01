import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1569: [7/45, 242/5, 5/77, 3/11, 539/2]

Vector representation:
```
 0 -2 -1  1  0
 1  0 -1  0  2
 0  0  1 -1 -1
 0  1  0  0 -1
-1  0  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1569

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | _ => none

-- R4 chain: transfer e to b
theorem r4_chain : ∀ k, ∀ a b, ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih
  · intro a b; exists 0
  · intro a b; rw [Nat.add_succ]
    step fm
    apply stepStar_trans (ih a (b + 1)); ring_nf; finish

-- R2-R3 chain with b=0
theorem r2r3_b0 : ∀ k, ∀ a d e, ⟨a, 0, 1, d + k, e⟩ [fm]⊢* ⟨a + k, 0, 1, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 1)); ring_nf; finish

-- R2-R3 chain with b=1
theorem r2r3_b1 : ∀ k, ∀ a d e, ⟨a, 1, 1, d + k, e⟩ [fm]⊢* ⟨a + k, 1, 1, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) d (e + 1)); ring_nf; finish

-- R5-R3-R1 chain: each round does a-1, b-2, d+2
theorem r531_chain : ∀ k, ∀ a b d, ⟨a + k, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a b d; exists 0
  · intro a b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a b (d + 2)); ring_nf; finish

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨3 * n ^ 2 + 6 * n + 4, 6 * n + 6, 0, 0, 0⟩ [fm]⊢⁺
    ⟨3 * n ^ 2 + 12 * n + 13, 6 * n + 12, 0, 0, 0⟩ := by
  -- Phase 1: R5-R3-R1 chain (3n+3 rounds)
  rw [show 3 * n ^ 2 + 6 * n + 4 = (3 * n ^ 2 + 3 * n + 1) + (3 * n + 3) from by ring,
      show 6 * n + 6 = 0 + 2 * (3 * n + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r531_chain (3 * n + 3) (3 * n ^ 2 + 3 * n + 1) 0 0)
  rw [show 0 + 2 * (3 * n + 3) = 6 * n + 6 from by ring]
  -- Phase 2: R5
  rw [show 3 * n ^ 2 + 3 * n + 1 = (3 * n ^ 2 + 3 * n) + 1 from by ring]
  step fm
  -- Phase 3: R3
  step fm
  -- Phase 4: R2-R3 chain b=0 (6n+7 rounds)
  rw [show 6 * n + 7 = 0 + (6 * n + 7) from by ring]
  apply stepStar_trans (r2r3_b0 (6 * n + 7) (3 * n ^ 2 + 3 * n) 0 0)
  rw [show 3 * n ^ 2 + 3 * n + (6 * n + 7) = 3 * n ^ 2 + 9 * n + 7 from by ring,
      show 0 + (6 * n + 7) = 6 * n + 7 from by ring]
  -- Phase 5: final R2
  step fm
  -- Phase 6: R4 chain (6n+9 transfers)
  rw [show 3 * n ^ 2 + 9 * n + 7 + 1 = 3 * n ^ 2 + 9 * n + 8 from by ring,
      show 6 * n + 7 + 2 = 6 * n + 9 from by ring]
  apply stepStar_trans (r4_chain (6 * n + 9) (3 * n ^ 2 + 9 * n + 8) 0)
  rw [show 0 + (6 * n + 9) = 6 * n + 9 from by ring]
  -- Phase 7: R5-R3-R1 chain (3n+4 rounds)
  rw [show 3 * n ^ 2 + 9 * n + 8 = (3 * n ^ 2 + 6 * n + 4) + (3 * n + 4) from by ring,
      show 6 * n + 9 = 1 + 2 * (3 * n + 4) from by ring]
  apply stepStar_trans (r531_chain (3 * n + 4) (3 * n ^ 2 + 6 * n + 4) 1 0)
  rw [show 0 + 2 * (3 * n + 4) = 6 * n + 8 from by ring]
  -- Phase 8: R5
  rw [show 3 * n ^ 2 + 6 * n + 4 = (3 * n ^ 2 + 6 * n + 3) + 1 from by ring]
  step fm
  -- Phase 9: R3
  step fm
  -- Phase 10: R2-R3 chain b=1 (6n+9 rounds)
  rw [show 6 * n + 9 = 0 + (6 * n + 9) from by ring]
  apply stepStar_trans (r2r3_b1 (6 * n + 9) (3 * n ^ 2 + 6 * n + 3) 0 0)
  rw [show 3 * n ^ 2 + 6 * n + 3 + (6 * n + 9) = 3 * n ^ 2 + 12 * n + 12 from by ring,
      show 0 + (6 * n + 9) = 6 * n + 9 from by ring]
  -- Phase 11: final R2
  step fm
  -- Phase 12: R4 chain (6n+11 transfers)
  rw [show 3 * n ^ 2 + 12 * n + 12 + 1 = 3 * n ^ 2 + 12 * n + 13 from by ring,
      show 6 * n + 9 + 2 = 6 * n + 11 from by ring]
  apply stepStar_trans (r4_chain (6 * n + 11) (3 * n ^ 2 + 12 * n + 13) 1)
  rw [show 1 + (6 * n + 11) = 6 * n + 12 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 6, 0, 0, 0⟩) (by execute fm 25)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n : ℕ, q = ⟨3 * n ^ 2 + 6 * n + 4, 6 * n + 6, 0, 0, 0⟩)
  · intro c ⟨n, hc⟩; subst hc
    exact ⟨⟨3 * n ^ 2 + 12 * n + 13, 6 * n + 12, 0, 0, 0⟩,
      ⟨n + 1, by ring_nf⟩, main_trans n⟩
  · exact ⟨0, by norm_num⟩

end Sz22_2003_unofficial_1569
