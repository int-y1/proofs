import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1284: [56/15, 9/7, 1/6, 125/2, 7/5]

Vector representation:
```
 3 -1 -1  1
 0  2  0 -1
-1 -1  0  0
-1  0  3  0
 0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1284

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+3, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- R4 chain: drain a, producing c (b=0, d=0)
theorem r4_chain : ∀ k, ∀ c, ⟨k, (0 : ℕ), c, (0 : ℕ)⟩ [fm]⊢* ⟨0, 0, c + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · ring_nf; finish
  · rw [show c + 3 * (k + 1) = (c + 3) + 3 * k from by ring]
    step fm
    apply stepStar_trans (ih (c + 3))
    ring_nf; finish

-- R2R1R1 interleaved chain: each round R2,R1,R1
theorem r2r1r1_chain : ∀ k, ∀ a c d, ⟨a, (0 : ℕ), c + 2 * k, d + 1⟩ [fm]⊢*
    ⟨a + 6 * k, 0, c, d + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by ring,
        show d + 1 = d + 1 from rfl]
    step fm; step fm; step fm
    rw [show a + 6 * (k + 1) = (a + 6) + 6 * k from by ring,
        show d + (k + 1) + 1 = (d + 1) + k + 1 from by ring]
    apply stepStar_trans (ih (a + 6) c (d + 1))
    ring_nf; finish

-- R2 drain: d to b (c=0)
theorem r2_drain : ∀ k, ∀ a b, ⟨a, b, (0 : ℕ), k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2))
    ring_nf; finish

-- R3 drain: consume a and b equally (c=0, d=0)
theorem r3_drain : ∀ k, ∀ a, ⟨a + k, k, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a)
    ring_nf; finish

-- Transition for odd a: (2K+1, 0, 0, 0) ⊢⁺ (12K+2, 0, 0, 0)
theorem transition_odd (K : ℕ) :
    ⟨2 * K + 1, (0 : ℕ), 0, 0⟩ [fm]⊢⁺ ⟨12 * K + 2, 0, 0, 0⟩ := by
  -- Phase 1: R4 chain
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * K + 1) 0)
  rw [show 0 + 3 * (2 * K + 1) = 6 * K + 3 from by ring]
  -- Phase 2: Opening R5, R2, R1, R1
  rw [show 6 * K + 3 = (6 * K + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, (6 * K + 2) + 1, 0⟩ : Q) [fm]⊢ ⟨0, 0, 6 * K + 2, 1⟩)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show 6 * K + 2 = (6 * K + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show 6 * K + 1 = (6 * K) + 1 from by ring]
  step fm
  -- State: (6, 0, 6K, 2)
  rw [show 6 * K = 0 + 2 * (3 * K) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r2r1r1_chain (3 * K) 6 0 1)
  rw [show 6 + 6 * (3 * K) = 18 * K + 6 from by ring,
      show 1 + 3 * K + 1 = 3 * K + 2 from by ring]
  -- State: (18K+6, 0, 0, 3K+2)
  apply stepStar_trans (r2_drain (3 * K + 2) (18 * K + 6) 0)
  rw [show 0 + 2 * (3 * K + 2) = 6 * K + 4 from by ring]
  -- State: (18K+6, 6K+4, 0, 0)
  rw [show 18 * K + 6 = (12 * K + 2) + (6 * K + 4) from by ring]
  exact r3_drain (6 * K + 4) (12 * K + 2)

-- Transition for even a: (2K+2, 0, 0, 0) ⊢⁺ (12K+8, 0, 0, 0)
theorem transition_even (K : ℕ) :
    ⟨2 * K + 2, (0 : ℕ), 0, 0⟩ [fm]⊢⁺ ⟨12 * K + 8, 0, 0, 0⟩ := by
  -- Phase 1: R4 chain
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * K + 2) 0)
  rw [show 0 + 3 * (2 * K + 2) = 6 * K + 6 from by ring]
  -- Phase 2: Opening R5, R2, R1, R1
  rw [show 6 * K + 6 = (6 * K + 5) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 0, (6 * K + 5) + 1, 0⟩ : Q) [fm]⊢ ⟨0, 0, 6 * K + 5, 1⟩)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show 6 * K + 5 = (6 * K + 4) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show 6 * K + 4 = (6 * K + 3) + 1 from by ring]
  step fm
  -- State: (6, 0, 6K+3, 2)
  rw [show 6 * K + 3 = 1 + 2 * (3 * K + 1) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r2r1r1_chain (3 * K + 1) 6 1 1)
  rw [show 6 + 6 * (3 * K + 1) = 18 * K + 12 from by ring,
      show 1 + (3 * K + 1) + 1 = 3 * K + 3 from by ring]
  -- State: (18K+12, 0, 1, 3K+3)
  -- R2: (18K+12, 2, 1, 3K+2)
  rw [show 3 * K + 3 = (3 * K + 2) + 1 from by ring]
  step fm
  -- R1: (18K+15, 1, 0, 3K+3)
  step fm
  rw [show 18 * K + 12 + 3 = 18 * K + 15 from by ring,
      show 3 * K + 2 + 1 = 3 * K + 3 from by ring]
  -- State: (18K+15, 1, 0, 3K+3)
  apply stepStar_trans (r2_drain (3 * K + 3) (18 * K + 15) 1)
  rw [show 1 + 2 * (3 * K + 3) = 6 * K + 7 from by ring]
  -- State: (18K+15, 6K+7, 0, 0)
  rw [show 18 * K + 15 = (12 * K + 8) + (6 * K + 7) from by ring]
  exact r3_drain (6 * K + 7) (12 * K + 8)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a, a ≥ 1 ∧ q = ⟨a, 0, 0, 0⟩)
  · intro q ⟨a, ha, hq⟩
    subst hq
    rcases Nat.even_or_odd a with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      rcases K with _ | K
      · omega
      · refine ⟨⟨12 * K + 8, 0, 0, 0⟩, ⟨12 * K + 8, by omega, rfl⟩, ?_⟩
        have := transition_even K
        convert this using 2
    · subst hK
      refine ⟨⟨12 * K + 2, 0, 0, 0⟩, ⟨12 * K + 2, by omega, rfl⟩, ?_⟩
      have := transition_odd K
      convert this using 2
  · exact ⟨1, by omega, rfl⟩

end Sz22_2003_unofficial_1284
