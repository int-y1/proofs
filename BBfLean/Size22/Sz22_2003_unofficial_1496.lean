import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1496: [7/15, 9/77, 22/3, 25/11, 847/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1 -1  0  0  1
 0  0  2  0 -1
-1  0  0  1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1496

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | _ => none

-- R3 chain: drain b, building a and e.
theorem r3_chain : ∀ k a b e, ⟨a, b + k, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (e + 1))
    ring_nf; finish

-- R4 chain: drain e, building c.
theorem r4_chain : ∀ k a c e, ⟨a, (0 : ℕ), c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) e)
    ring_nf; finish

-- R5+R1+R2 drain round: each round consumes 1 from a, 4 from c, adds 3 to d.
theorem r5_drain : ∀ k a c d, ⟨a + k, (0 : ℕ), c + 4 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring,
        show (c + 4 * k) + 4 = (c + 4 * k + 2) + 2 from by ring]
    step fm; step fm
    rw [show (c + 4 * k + 2 : ℕ) + 2 = (c + 4 * k) + 2 + 2 from by ring]
    step fm; step fm
    rw [show (c + 4 * k) + 2 = (c + 4 * k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3))
    ring_nf; finish

-- Even final: after R5 drain produces (a+1, 0, 0, d+1, 0), do R5+R2+R2.
theorem even_final (a d : ℕ) :
    ⟨a + 1, (0 : ℕ), 0, d + 1, 0⟩ [fm]⊢* ⟨a, 4, 0, d, 0⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

-- Odd cleanup: from (a+1, 0, 2, d, 0) to (a+1, 3, 0, d, 0) in 7 steps.
theorem odd_cleanup (a d : ℕ) :
    ⟨a + 1, (0 : ℕ), 2, d, 0⟩ [fm]⊢* ⟨a + 1, 3, 0, d, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- R3/R2 alternating chain: from (a, b+1, 0, d+k, 0) to (a+k, b+k+1, 0, d, 0).
theorem r3r2_chain : ∀ k a b d, ⟨a, b + 1, (0 : ℕ), d + k, 0⟩ [fm]⊢* ⟨a + k, b + k + 1, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; simp; exists 0
  | succ k ih =>
    intro a b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 1) d)
    ring_nf; finish

-- Even case: b = 2j. (a+1, 2j+1, 0, 0, 0) ⊢⁺ (a+4j+2, 3j+3, 0, 0, 0).
theorem main_even (a j : ℕ) :
    ⟨a + 1, 2 * j + 1, (0 : ℕ), 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * j + 2, 3 * j + 3, 0, 0, 0⟩ := by
  -- Phase 1: R3 chain (2j+1 steps)
  rw [show (2 * j + 1 : ℕ) = 0 + (2 * j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * j + 1) (a + 1) 0 0)
  rw [show a + 1 + (2 * j + 1) = a + 2 * j + 2 from by ring,
      show (0 : ℕ) + (2 * j + 1) = 0 + (2 * j + 1) from by ring]
  -- Phase 2: R4 chain (2j+1 steps)
  apply step_stepStar_stepPlus (by show _ [fm]⊢ _; rfl)
  apply stepStar_trans (r4_chain (2 * j) (a + 2 * j + 2) 2 0)
  rw [show 2 + 2 * (2 * j) = 4 * j + 2 from by ring]
  -- State: (a+2j+2, 0, 4j+2, 0, 0)
  -- Phase 3: R5 drain (j rounds)
  rw [show a + 2 * j + 2 = (a + j + 2) + j from by ring,
      show 4 * j + 2 = 2 + 4 * j from by ring]
  apply stepStar_trans (r5_drain j (a + j + 2) 2 0)
  rw [show (0 : ℕ) + 3 * j = 3 * j from by ring]
  -- State: (a+j+2, 0, 2, 3j, 0)
  -- Phase 4: Odd cleanup (7 steps)
  rw [show a + j + 2 = (a + j + 1) + 1 from by ring]
  apply stepStar_trans (odd_cleanup (a + j + 1) (3 * j))
  -- State: (a+j+2, 3, 0, 3j, 0)
  -- Phase 5: R3/R2 chain (3j pairs)
  rw [show a + j + 1 + 1 = a + j + 2 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show 3 * j = 0 + 3 * j from by ring]
  apply stepStar_trans (r3r2_chain (3 * j) (a + j + 2) 2 0)
  ring_nf; finish

-- Odd case: b = 2j+1. (a+1, 2j+2, 0, 0, 0) ⊢⁺ (a+4j+3, 3j+6, 0, 0, 0).
theorem main_odd (a j : ℕ) :
    ⟨a + 1, 2 * j + 2, (0 : ℕ), 0, 0⟩ [fm]⊢⁺ ⟨a + 4 * j + 3, 3 * j + 6, 0, 0, 0⟩ := by
  -- Phase 1: R3 chain (2j+2 steps)
  rw [show (2 * j + 2 : ℕ) = 0 + (2 * j + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * j + 2) (a + 1) 0 0)
  rw [show a + 1 + (2 * j + 2) = a + 2 * j + 3 from by ring,
      show (0 : ℕ) + (2 * j + 2) = 0 + (2 * j + 2) from by ring]
  -- Phase 2: R4 chain (2j+2 steps)
  apply step_stepStar_stepPlus (by show _ [fm]⊢ _; rfl)
  apply stepStar_trans (r4_chain (2 * j + 1) (a + 2 * j + 3) 2 0)
  rw [show 2 + 2 * (2 * j + 1) = 4 * j + 4 from by ring]
  -- State: (a+2j+3, 0, 4j+4, 0, 0)
  -- Phase 3: R5 drain (j+1 rounds)
  rw [show a + 2 * j + 3 = (a + j + 2) + (j + 1) from by ring,
      show 4 * j + 4 = 0 + 4 * (j + 1) from by ring]
  apply stepStar_trans (r5_drain (j + 1) (a + j + 2) 0 0)
  rw [show (0 : ℕ) + 3 * (j + 1) = 3 * j + 3 from by ring]
  -- State: (a+j+2, 0, 0, 3j+3, 0)
  -- Phase 4: Even final (3 steps: R5+R2+R2)
  rw [show a + j + 2 = (a + j + 1) + 1 from by ring,
      show 3 * j + 3 = (3 * j + 2) + 1 from by ring]
  apply stepStar_trans (even_final (a + j + 1) (3 * j + 2))
  -- State: (a+j+1, 4, 0, 3j+2, 0)
  -- Phase 5: R3/R2 chain (3j+2 pairs)
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 3 * j + 2 = 0 + (3 * j + 2) from by ring]
  apply stepStar_trans (r3r2_chain (3 * j + 2) (a + j + 1) 3 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 6, 0, 0, 0⟩) (by execute fm 27)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a b, q = ⟨a + 1, b + 1, (0 : ℕ), 0, 0⟩)
  · intro q ⟨a, b, hq⟩
    subst hq
    rcases Nat.even_or_odd b with ⟨j, hj⟩ | ⟨j, hj⟩
    · subst hj
      rw [show j + j = 2 * j from by ring]
      exact ⟨⟨a + 4 * j + 2, 3 * j + 3, 0, 0, 0⟩,
        ⟨a + 4 * j + 1, 3 * j + 2, by ring_nf⟩,
        main_even a j⟩
    · subst hj
      rw [show 2 * j + 1 + 1 = 2 * j + 2 from by ring]
      exact ⟨⟨a + 4 * j + 3, 3 * j + 6, 0, 0, 0⟩,
        ⟨a + 4 * j + 2, 3 * j + 5, by ring_nf⟩,
        main_odd a j⟩
  · exact ⟨3, 5, by ring_nf⟩

end Sz22_2003_unofficial_1496
