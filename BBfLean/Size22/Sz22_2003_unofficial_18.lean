import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #18: [1/135, 2/15, 63/2, 125/7, 3/5]

Vector representation:
```
 0 -3 -1  0
 1 -1 -1  0
-1  2  0  1
 0  0  3 -1
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_18

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+3, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b+2, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 chain: drain d into c
theorem r4_chain : ∀ k, ∀ c d, ⟨0, 0, c, d + k⟩ [fm]⊢* ⟨0, 0, c + 3 * k, d⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 drain: drain a into b,d
theorem r3_drain : ∀ k, ∀ a b d, ⟨a + k, b, 0, d⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4+3R1 drain: each round subtracts 9 from b and 1 from d
theorem drain_9 : ∀ j, ∀ b d, ⟨0, b + 9 * j, 0, d + j⟩ [fm]⊢* ⟨0, b, 0, d⟩ := by
  intro j; induction' j with j ih <;> intro b d
  · exists 0
  rw [show b + 9 * (j + 1) = (b + 9 * j) + 9 from by ring,
      show d + (j + 1) = (d + j) + 1 from by ring]
  step fm
  rw [show b + 9 * j + 9 = (b + 9 * j + 6) + 3 from by ring]
  step fm
  rw [show b + 9 * j + 6 = (b + 9 * j + 3) + 3 from by ring]
  step fm
  rw [show b + 9 * j + 3 = (b + 9 * j) + 3 from by ring]
  step fm
  exact ih _ _

-- Interleaved R3,R2,R2 chain + R3 drain:
-- From (k+1, 0, c, k) we reach (0, c + 2*k + 2, 0, c + 2*k + 1)
-- Proved by induction on c with step 2 + handling c=0 and c=1 base cases
theorem interleaved : ∀ c, ∀ k, ⟨k + 1, 0, c, k⟩ [fm]⊢* ⟨0, c + 2 * k + 2, 0, c + 2 * k + 1⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ihc; intro k
  rcases c with _ | _ | c
  · -- c = 0: R3 drain from (k+1, 0, 0, k) to (0, 2k+2, 0, 2k+1)
    rw [show k + 1 = 0 + (k + 1) from by ring,
        show (0 : ℕ) + 2 * k + 2 = 0 + 2 * (k + 1) from by ring,
        show (0 : ℕ) + 2 * k + 1 = k + (k + 1) from by ring]
    exact r3_drain (k + 1) 0 0 k
  · -- c = 1: (k+1, 0, 1, k) -R3-> (k, 2, 1, k+1) -R2-> (k+1, 1, 0, k+1)
    -- Then R3 drain from (k+1, 1, 0, k+1)
    step fm; step fm
    have h := r3_drain (k + 1) 0 1 (k + 1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  · -- c + 2: R3,R2,R2 gives (k+2, 0, c, k+1), then apply ihc
    step fm; step fm; step fm
    apply stepStar_trans (ihc c (by omega) (k + 1))
    ring_nf; finish

-- Full phase: (0, 0, C + 2, 0) →* (0, C + 2, 0, C + 1)
-- Via R5,R2 then interleaved
theorem full_phase : ∀ C, ⟨0, 0, C + 2, 0⟩ [fm]⊢* ⟨0, C + 2, 0, C + 1⟩ := by
  intro C
  step fm; step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (interleaved C 0)
  ring_nf; finish

-- Tail for b=5: (0, 5, 0, E+1) →* (0, 0, 2, E+2)
theorem tail_5 : ∀ E, ⟨0, 5, 0, E + 1⟩ [fm]⊢* ⟨0, 0, 2, E + 2⟩ := by
  intro E
  execute fm 14

-- Tail for b=8: (0, 8, 0, E+2) → (0, 0, 2, E+1)
theorem tail_8 : ∀ E, ⟨0, 8, 0, E + 2⟩ [fm]⊢* ⟨0, 0, 2, E + 1⟩ := by
  intro E
  execute fm 7

-- Tail for b=2: (0, 2, 0, E+1) → (0, 5, 0, E+3) → (0, 0, 2, E+4)
theorem tail_2 : ∀ E, ⟨0, 2, 0, E + 1⟩ [fm]⊢* ⟨0, 0, 2, E + 4⟩ := by
  intro E
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  -- Now at (0, 5, 0, E+3)
  apply stepStar_trans (tail_5 (E + 2))
  ring_nf; finish

-- Transition for d ≡ 1 mod 3: d = 3k+1
-- (0,0,2,3k+1) →⁺ (0,0,2,8k+5)
theorem trans_mod1 (k : ℕ) : ⟨0, 0, 2, 3 * k + 1⟩ [fm]⊢⁺ ⟨0, 0, 2, 8 * k + 5⟩ := by
  -- Phase 1: R4 chain (3k+1 steps): (0,0,2,3k+1) → (0,0,9k+5,0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2, 3 * k + 1⟩ = some ⟨0, 0, 5, 3 * k⟩
    simp [fm]
  rw [show 3 * k = 0 + (3 * k) from by ring,
      show (5 : ℕ) = 2 + 3 * 1 from by ring,
      show 2 + 3 * 1 = 2 + 3 * 1 from rfl]
  apply stepStar_trans (r4_chain (3 * k) (2 + 3 * 1) 0)
  -- Now at (0, 0, 9k+5, 0)
  -- Phase 2: full_phase: (0,0,9k+5,0) → (0, 9k+5, 0, 9k+4)
  rw [show 2 + 3 * 1 + 3 * (3 * k) = (9 * k + 3) + 2 from by ring]
  apply stepStar_trans (full_phase (9 * k + 3))
  -- Now at (0, 9k+5, 0, 9k+4)
  -- Phase 3: drain_9 (k rounds): (0, 9k+5, 0, 9k+4) → (0, 5, 0, 8k+4)
  rw [show 9 * k + 3 + 2 = 5 + 9 * k from by ring,
      show 9 * k + 3 + 1 = (8 * k + 4) + k from by ring]
  apply stepStar_trans (drain_9 k 5 (8 * k + 4))
  -- Now at (0, 5, 0, 8k+4)
  -- Phase 4: tail_5: (0, 5, 0, 8k+4) → (0, 0, 2, 8k+5)
  rw [show 8 * k + 4 = (8 * k + 3) + 1 from by ring]
  apply stepStar_trans (tail_5 (8 * k + 3))
  ring_nf; finish

-- Transition for d ≡ 2 mod 3: d = 3k+2
-- (0,0,2,3k+2) →⁺ (0,0,2,8k+6)
theorem trans_mod2 (k : ℕ) : ⟨0, 0, 2, 3 * k + 2⟩ [fm]⊢⁺ ⟨0, 0, 2, 8 * k + 6⟩ := by
  -- Phase 1: R4 chain (3k+2 steps): (0,0,2,3k+2) → (0,0,9k+8,0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2, 3 * k + 2⟩ = some ⟨0, 0, 5, 3 * k + 1⟩
    simp [fm]
  rw [show 3 * k + 1 = 0 + (3 * k + 1) from by ring]
  apply stepStar_trans (r4_chain (3 * k + 1) 5 0)
  -- Now at (0, 0, 9k+8, 0)
  rw [show 5 + 3 * (3 * k + 1) = (9 * k + 6) + 2 from by ring]
  apply stepStar_trans (full_phase (9 * k + 6))
  -- Now at (0, 9k+8, 0, 9k+7)
  rw [show 9 * k + 6 + 2 = 8 + 9 * k from by ring,
      show 9 * k + 6 + 1 = (8 * k + 7) + k from by ring]
  apply stepStar_trans (drain_9 k 8 (8 * k + 7))
  -- Now at (0, 8, 0, 8k+7)
  rw [show 8 * k + 7 = (8 * k + 5) + 2 from by ring]
  apply stepStar_trans (tail_8 (8 * k + 5))
  ring_nf; finish

-- Transition for d ≡ 0 mod 3: d = 3(k+1)
-- (0,0,2,3k+3) →⁺ (0,0,2,8k+12)
theorem trans_mod0 (k : ℕ) : ⟨0, 0, 2, 3 * k + 3⟩ [fm]⊢⁺ ⟨0, 0, 2, 8 * k + 12⟩ := by
  -- Phase 1: R4 chain (3k+3 steps): (0,0,2,3k+3) → (0,0,9k+11,0)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2, 3 * k + 3⟩ = some ⟨0, 0, 5, 3 * k + 2⟩
    simp [fm]
  rw [show 3 * k + 2 = 0 + (3 * k + 2) from by ring]
  apply stepStar_trans (r4_chain (3 * k + 2) 5 0)
  rw [show 5 + 3 * (3 * k + 2) = (9 * k + 9) + 2 from by ring]
  apply stepStar_trans (full_phase (9 * k + 9))
  -- Now at (0, 9k+11, 0, 9k+10)
  rw [show 9 * k + 9 + 2 = 2 + 9 * (k + 1) from by ring,
      show 9 * k + 9 + 1 = (8 * k + 9) + (k + 1) from by ring]
  apply stepStar_trans (drain_9 (k + 1) 2 (8 * k + 9))
  -- Now at (0, 2, 0, 8k+9)
  rw [show 8 * k + 9 = (8 * k + 8) + 1 from by ring]
  apply stepStar_trans (tail_2 (8 * k + 8))
  ring_nf; finish

-- Nonhalting proof
theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0) reaches (0,0,2,4) in some steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 4⟩) (by execute fm 22)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d, q = ⟨0, 0, 2, d⟩ ∧ d ≥ 1)
  · intro c ⟨d, hq, hd⟩; subst hq
    have hmod := Nat.div_add_mod d 3
    set q := d / 3
    set r := d % 3
    have hr : r < 3 := Nat.mod_lt d (by omega)
    interval_cases r
    · -- d ≡ 0 mod 3: d = 3q, q ≥ 1
      rcases q with _ | k
      · omega
      rw [show d = 3 * k + 3 from by omega]
      exact ⟨⟨0, 0, 2, 8 * k + 12⟩, ⟨8 * k + 12, rfl, by omega⟩, trans_mod0 k⟩
    · -- d ≡ 1 mod 3: d = 3q+1
      rw [show d = 3 * q + 1 from by omega]
      exact ⟨⟨0, 0, 2, 8 * q + 5⟩, ⟨8 * q + 5, rfl, by omega⟩, trans_mod1 q⟩
    · -- d ≡ 2 mod 3: d = 3q+2
      rw [show d = 3 * q + 2 from by omega]
      exact ⟨⟨0, 0, 2, 8 * q + 6⟩, ⟨8 * q + 6, rfl, by omega⟩, trans_mod2 q⟩
  · exact ⟨4, rfl, by omega⟩

end Sz22_2003_unofficial_18
