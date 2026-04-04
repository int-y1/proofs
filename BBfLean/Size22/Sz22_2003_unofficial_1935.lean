import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1935: [9/70, 275/7, 7/15, 2/11, 21/2]

Vector representation:
```
-1  2 -1 -1  0
 0  0  2 -1  1
 0 -1 -1  1  0
 1  0  0  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1935

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: drain e into a.
theorem e_to_a : ∀ k, ∀ a, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1))
    rw [show a + 1 + k = a + (k + 1) from by ring]; finish

-- R1+R3 chain: each round R1 then R3.
theorem r1r3_chain : ∀ k a b c, ⟨a + k, b + 1, c + 2 * k, 1, 0⟩ [fm]⊢* ⟨a, b + k + 1, c, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · simp; exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (a + 1) b (c + 2))
    step fm; step fm
    ring_nf; finish

-- Phase 4 loop: 5-step cycle (R2, R3, R1, R4, R5).
theorem phase4_loop : ∀ k a b, ⟨a + k, b + 1, 0, 1, 0⟩ [fm]⊢* ⟨a, b + 2 * k + 1, 0, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · simp; exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring]
    apply stepStar_trans (ih (a + 1) b)
    step fm; step fm; step fm; step fm; step fm
    ring_nf; finish

-- R3+R2 chain: drain b, grow c and e.
theorem r3r2_chain : ∀ k b e, ⟨0, b + k, c + 1, 0, e⟩ [fm]⊢* ⟨0, b, c + k + 1, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · simp; exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih (b + 1) e)
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    step fm; step fm
    ring_nf; finish

-- Full transition for odd n = 2k+5:
-- (0, 0, 2k+6, 0, 2k+5) ⊢⁺ (0, 0, 3k+8, 0, 3k+7).
theorem odd_trans (k : ℕ) : ⟨0, 0, 2 * k + 6, 0, 2 * k + 5⟩ [fm]⊢⁺
    ⟨0, 0, 3 * k + 8, 0, 3 * k + 7⟩ := by
  -- Phase 1: R4^(2k+5): (0,0,2k+6,0,2k+5) -> (2k+5, 0, 2k+6, 0, 0)
  rw [show (2 * k + 5 : ℕ) = 0 + (2 * k + 5) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_a (c := 2 * k + 6) (e := 0) (2 * k + 5) 0)
  -- Now goal: (2k+5, 0, 2k+6, 0, 0) ⊢⁺ target
  -- Phase 2: R5: (2k+5, 0, 2k+6, 0, 0) -> (2k+4, 1, 2k+6, 1, 0)
  rw [show 0 + (2 * k + 5) = (2 * k + 4) + 1 from by ring]
  step fm
  -- Phase 3: R1+R3^(k+2): (2k+4, 1, 2k+6, 1, 0) -> (k+2, k+3, 2, 1, 0)
  rw [show 2 * k + 6 = 2 + 2 * (k + 2) from by ring,
      show 2 * k + 4 = (k + 2) + (k + 2) from by ring]
  apply stepStar_trans (r1r3_chain (k + 2) (k + 2) 0 2)
  -- Phase 3b: R1, R3: (k+2, k+3, 2, 1, 0) -> (k+1, k+5, 0, 1, 0)
  rw [show 0 + (k + 2) + 1 = k + 3 from by ring]
  step fm; step fm
  -- Phase 4: loop (k+1) times: (k+1, k+4, 0, 1, 0) -> (0, 3k+6, 0, 1, 0)
  -- The state is (k+1, k+4, 0, 1, 0). phase4_loop needs (a+k, b+1, 0, 1, 0).
  -- a=0, iter=k+1, b+1=k+4 -> not matching directly. Use rw.
  rw [show k + 1 = 0 + (k + 1) from by ring,
      show (k + 4 : ℕ) = (k + 3) + 1 from by ring]
  apply stepStar_trans (phase4_loop (k + 1) 0 (k + 3))
  -- Phase 5: R2, then R3+R2 chain
  rw [show k + 3 + 2 * (k + 1) + 1 = 3 * k + 6 from by ring]
  step fm
  rw [show (3 * k + 6 : ℕ) = 0 + (3 * k + 6) from by ring]
  apply stepStar_trans (r3r2_chain (c := 1) (3 * k + 6) 0 1)
  ring_nf; finish

-- Full transition for even n = 2k+6:
-- (0, 0, 2k+7, 0, 2k+6) ⊢⁺ (0, 0, 3k+9, 0, 3k+8).
theorem even_trans (k : ℕ) : ⟨0, 0, 2 * k + 7, 0, 2 * k + 6⟩ [fm]⊢⁺
    ⟨0, 0, 3 * k + 9, 0, 3 * k + 8⟩ := by
  -- Phase 1: R4^(2k+6): -> (2k+6, 0, 2k+7, 0, 0)
  rw [show (2 * k + 6 : ℕ) = 0 + (2 * k + 6) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_a (c := 2 * k + 7) (e := 0) (2 * k + 6) 0)
  -- Phase 2: R5: -> (2k+5, 1, 2k+7, 1, 0)
  rw [show 0 + (2 * k + 6) = (2 * k + 5) + 1 from by ring]
  step fm
  -- Phase 3: R1+R3^(k+3): -> (k+2, k+4, 1, 1, 0)
  rw [show 2 * k + 7 = 1 + 2 * (k + 3) from by ring,
      show 2 * k + 5 = (k + 2) + (k + 3) from by ring]
  apply stepStar_trans (r1r3_chain (k + 3) (k + 2) 0 1)
  -- Phase 3b: R1: -> (k+1, k+6, 0, 0, 0)
  rw [show 0 + (k + 3) + 1 = k + 4 from by ring]
  step fm
  -- Phase 3c: R5: -> (k, k+7, 0, 1, 0)
  step fm
  -- Phase 4: loop k times: -> (0, 3k+7, 0, 1, 0)
  -- State: (k, 0+k+4+2+1, 0, 1, 0). Need to match (0+k, b+1, 0, 1, 0).
  rw [show (k : ℕ) = 0 + k from by ring,
      show 0 + k + 4 + 2 + 1 = (k + 6) + 1 from by ring]
  apply stepStar_trans (phase4_loop k 0 (k + 6))
  -- Phase 5: R2 then R3+R2^(3k+7)
  rw [show k + 6 + 2 * k + 1 = 3 * k + 7 from by ring]
  step fm
  rw [show (3 * k + 7 : ℕ) = 0 + (3 * k + 7) from by ring]
  apply stepStar_trans (r3r2_chain (c := 1) (3 * k + 7) 0 1)
  ring_nf; finish

-- Main theorem
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 6, 0, 5⟩) (by execute fm 49)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, n + 1, 0, n⟩ ∧ n ≥ 5)
  · intro c ⟨n, hq, hn⟩; subst hq
    rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
    · -- n even: n = 2K, K >= 3
      rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 3 := ⟨K - 3, by omega⟩
      refine ⟨⟨0, 0, 3 * k + 9, 0, 3 * k + 8⟩,
        ⟨3 * k + 8, rfl, by omega⟩, ?_⟩
      show ⟨0, 0, 2 * (k + 3) + 1, 0, 2 * (k + 3)⟩ [fm]⊢⁺ ⟨0, 0, 3 * k + 9, 0, 3 * k + 8⟩
      rw [show 2 * (k + 3) + 1 = 2 * k + 7 from by ring,
          show 2 * (k + 3) = 2 * k + 6 from by ring]
      exact even_trans k
    · -- n odd: n = 2K + 1, K >= 2
      subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
      refine ⟨⟨0, 0, 3 * k + 8, 0, 3 * k + 7⟩,
        ⟨3 * k + 7, rfl, by omega⟩, ?_⟩
      show ⟨0, 0, 2 * (k + 2) + 2, 0, 2 * (k + 2) + 1⟩ [fm]⊢⁺ ⟨0, 0, 3 * k + 8, 0, 3 * k + 7⟩
      rw [show 2 * (k + 2) + 2 = 2 * k + 6 from by ring,
          show 2 * (k + 2) + 1 = 2 * k + 5 from by ring]
      exact odd_trans k
  · exact ⟨5, rfl, by omega⟩
