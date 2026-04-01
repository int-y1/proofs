import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1480: [7/15, 44/3, 9/77, 25/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0  1
 0  2  0 -1 -1
 0  0  2  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1480

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- Phase 1: c-drain loop. Each round: R5, R1, R3, R1, R1.
-- (a+k, 0, c+3*k, d, 0) ⊢* (a, 0, c, d+2*k, 0)
theorem c_drain : ∀ k, ∀ a c d, ⟨a + k, 0, c + 3 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 3 * (k + 1) = (c + 3 * k) + 1 + 1 + 1 from by ring]
    step fm  -- R5
    step fm  -- R1
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih a c (d + 2))
    ring_nf; finish

-- Phase 2a: r=0 exit. R5, R2.
-- (a+1, 0, 0, d, 0) ⊢⁺ (a+2, 0, 0, d, 2)
theorem r0_exit : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, d, 2⟩ := by
  step fm  -- R5
  step fm  -- R2
  finish

-- Phase 2b: r=1 exit. R5, R1, R3, R2, R2.
-- (a+1, 0, 1, d, 0) ⊢⁺ (a+4, 0, 0, d, 2)
theorem r1_exit : ⟨a + 1, 0, 1, d, 0⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, d, 2⟩ := by
  step fm  -- R5
  step fm  -- R1
  step fm  -- R3
  step fm  -- R2
  step fm  -- R2
  finish

-- Phase 2c: r=2 exit. R5, R1, R3, R1, R2.
-- (a+1, 0, 2, d, 0) ⊢⁺ (a+2, 0, 0, d+1, 1)
theorem r2_exit : ⟨a + 1, 0, 2, d, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, d + 1, 1⟩ := by
  step fm  -- R5
  step fm  -- R1
  step fm  -- R3
  step fm  -- R1
  step fm  -- R2
  finish

-- Phase 3: R3, R2, R2 drain loop.
-- (a, 0, 0, k, e+1) ⊢* (a+4*k, 0, 0, 0, e+k+1)
theorem r23_drain : ∀ k, ∀ a e, ⟨a, 0, 0, k, e + 1⟩ [fm]⊢* ⟨a + 4 * k, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    apply stepStar_trans (ih (a + 4) (e + 1))
    ring_nf; finish

-- Phase 4: R4 chain.
-- (a, 0, c, 0, k) ⊢* (a, 0, c+2*k, 0, 0)
theorem r4_chain : ∀ k, ∀ a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm  -- R4
    apply stepStar_trans (ih a (c + 2))
    ring_nf; finish

-- Combined drain+R4 for d >= 1, e >= 1:
-- (a, 0, 0, k+1, e+1) ⊢* (a+4*(k+1), 0, 2*(e+k+2), 0, 0)
theorem drain_r4 (k e : ℕ) : ∀ a, ⟨a, 0, 0, k + 1, e + 1⟩ [fm]⊢* ⟨a + 4 * (k + 1), 0, 2 * (e + k + 2), 0, 0⟩ := by
  intro a
  apply stepStar_trans (r23_drain (k + 1) a e)
  rw [show e + (k + 1) + 1 = (e + k + 2 - 1) + 1 from by omega,
      show a + 4 * (k + 1) = a + 4 * (k + 1) from rfl]
  apply stepStar_trans (r4_chain (e + k + 2) (a + 4 * (k + 1)) 0)
  ring_nf; finish

-- Combined drain+R4 for d = 0, e >= 1:
-- (a, 0, 0, 0, e+1) ⊢* (a, 0, 2*(e+1), 0, 0)
theorem zero_drain_r4 (e : ℕ) : ∀ a, ⟨a, 0, 0, 0, e + 1⟩ [fm]⊢* ⟨a, 0, 2 * (e + 1), 0, 0⟩ := by
  intro a
  apply stepStar_trans (r4_chain (e + 1) a 0)
  ring_nf; finish

-- Full transition for c = 3*k, residue 0:
-- (a+k+1, 0, 3*k, 0, 0) ⊢⁺ (a+8*k+2, 0, 4*k+4, 0, 0)
theorem trans_r0 (a k : ℕ) : ⟨a + k + 1, 0, 3 * k, 0, 0⟩ [fm]⊢⁺ ⟨a + 8 * k + 2, 0, 4 * k + 4, 0, 0⟩ := by
  rcases k with _ | k
  · -- k=0: (a+1, 0, 0, 0, 0) ⊢⁺ (a+2, 0, 4, 0, 0)
    apply stepPlus_stepStar_stepPlus r0_exit
    apply zero_drain_r4 1
  · -- k+1 >= 1:
    -- c_drain (k+1) rounds: (a+k+1+1, 0, 3*(k+1), 0, 0) ⊢* (a+1, 0, 0, 2*(k+1), 0)
    rw [show a + (k + 1) + 1 = a + 1 + (k + 1) from by ring,
        show 3 * (k + 1) = 0 + 3 * (k + 1) from by ring]
    apply stepStar_stepPlus_stepPlus (c_drain (k + 1) (a + 1) 0 0)
    rw [show (0 + 2 * (k + 1) : ℕ) = 2 * k + 2 from by ring]
    -- r0_exit: (a+1, 0, 0, 2k+2, 0) ⊢⁺ (a+2, 0, 0, 2k+2, 2)
    apply stepPlus_stepStar_stepPlus r0_exit
    -- drain_r4: (a+2, 0, 0, 2k+2, 2) ⊢* (a+8k+10, 0, 4k+8, 0, 0)
    rw [show (2 * k + 2 : ℕ) = (2 * k + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (drain_r4 (2 * k + 1) 1 (a + 2))
    ring_nf; finish

-- Full transition for c = 3*k+1, residue 1:
-- (a+k+1, 0, 3*k+1, 0, 0) ⊢⁺ (a+8*k+4, 0, 4*k+4, 0, 0)
theorem trans_r1 (a k : ℕ) : ⟨a + k + 1, 0, 3 * k + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 8 * k + 4, 0, 4 * k + 4, 0, 0⟩ := by
  rcases k with _ | k
  · -- k=0: (a+1, 0, 1, 0, 0) ⊢⁺ (a+4, 0, 4, 0, 0)
    apply stepPlus_stepStar_stepPlus r1_exit
    apply zero_drain_r4 1
  · -- k+1 >= 1:
    rw [show a + (k + 1) + 1 = a + 1 + (k + 1) from by ring,
        show 3 * (k + 1) + 1 = 1 + 3 * (k + 1) from by ring]
    apply stepStar_stepPlus_stepPlus (c_drain (k + 1) (a + 1) 1 0)
    rw [show (0 + 2 * (k + 1) : ℕ) = 2 * k + 2 from by ring]
    apply stepPlus_stepStar_stepPlus r1_exit
    rw [show (2 * k + 2 : ℕ) = (2 * k + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (drain_r4 (2 * k + 1) 1 (a + 4))
    ring_nf; finish

-- Full transition for c = 3*k+2, residue 2:
-- (a+k+1, 0, 3*k+2, 0, 0) ⊢⁺ (a+8*k+6, 0, 4*k+4, 0, 0)
theorem trans_r2 (a k : ℕ) : ⟨a + k + 1, 0, 3 * k + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + 8 * k + 6, 0, 4 * k + 4, 0, 0⟩ := by
  -- c_drain k rounds: (a+k+1, 0, 3*k+2, 0, 0) ⊢* (a+1, 0, 2, 2*k, 0)
  rw [show a + k + 1 = a + 1 + k from by ring,
      show 3 * k + 2 = 2 + 3 * k from by ring]
  apply stepStar_stepPlus_stepPlus (c_drain k (a + 1) 2 0)
  rw [show (0 + 2 * k : ℕ) = 2 * k from by ring]
  -- r2_exit: (a+1, 0, 2, 2*k, 0) ⊢⁺ (a+2, 0, 0, 2*k+1, 1)
  apply stepPlus_stepStar_stepPlus r2_exit
  -- drain_r4: (a+2, 0, 0, 2*k+1, 1) ⊢* (a+8*k+6, 0, 4*k+4, 0, 0)
  rw [show (2 * k + 1 : ℕ) = (2 * k) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain_r4 (2 * k) 0 (a + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 4, 0, 0⟩)
  · execute fm 4
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a + 1, 0, c, 0, 0⟩ ∧ c ≤ 3 * a + 2)
  · intro q ⟨a, c, hq, hinv⟩; subst hq
    have h3 : c % 3 < 3 := Nat.mod_lt _ (by omega)
    obtain ⟨k, hk⟩ : ∃ k, c = 3 * k + c % 3 := ⟨c / 3, by omega⟩
    interval_cases (c % 3)
    · -- c ≡ 0 (mod 3)
      rw [Nat.add_zero] at hk; subst hk
      obtain ⟨F, rfl⟩ : ∃ F, a = F + k := ⟨a - k, by omega⟩
      exact ⟨⟨F + 8 * k + 2, 0, 4 * k + 4, 0, 0⟩,
        ⟨F + 8 * k + 1, 4 * k + 4, by ring_nf, by omega⟩,
        trans_r0 F k⟩
    · -- c ≡ 1 (mod 3)
      subst hk
      obtain ⟨F, rfl⟩ : ∃ F, a = F + k := ⟨a - k, by omega⟩
      exact ⟨⟨F + 8 * k + 4, 0, 4 * k + 4, 0, 0⟩,
        ⟨F + 8 * k + 3, 4 * k + 4, by ring_nf, by omega⟩,
        trans_r1 F k⟩
    · -- c ≡ 2 (mod 3)
      subst hk
      obtain ⟨F, rfl⟩ : ∃ F, a = F + k := ⟨a - k, by omega⟩
      exact ⟨⟨F + 8 * k + 6, 0, 4 * k + 4, 0, 0⟩,
        ⟨F + 8 * k + 5, 4 * k + 4, by ring_nf, by omega⟩,
        trans_r2 F k⟩
  · exact ⟨1, 4, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1480
