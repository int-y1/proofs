import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1469: [7/15, 3/847, 50/7, 11/5, 45/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -2
 1  0  2 -1  0
 0  0 -1  0  1
-1  2  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1469

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | _ => none

-- Drain even: R5+R1+R2 repeated k times.
theorem drain_even : ∀ k, ⟨a + k, b, 0, 0, 2 * k⟩ [fm]⊢*
    ⟨a, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a := a) (b := b + 2))
    ring_nf; finish

-- Drain odd: R5+R1+R2 repeated k times, residual e=1.
theorem drain_odd : ∀ k, ⟨a + k, b, 0, 0, 2 * k + 1⟩ [fm]⊢*
    ⟨a, b + 2 * k, 0, 0, 1⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a := a) (b := b + 2))
    ring_nf; finish

-- Interleaved R1+R1+R3 with e=0.
-- One round: (A, b+2, 2, D, 0) →⁺ (A+1, b, 2, D+1, 0)
-- We present b+2 as the sum so step fm can see the +1 pattern.
theorem round_e0 : ⟨A, b + 2, 2, D, 0⟩ [fm]⊢⁺ ⟨A + 1, b, 2, D + 1, 0⟩ := by
  step fm  -- R1: (A, b+1, 1, D+1, 0)
  step fm  -- R1: (A, b, 0, D+2, 0)
  step fm  -- R3: (A+1, b, 2, D+1, 0)
  finish

-- Interleaved chain with e=0 by induction on k.
-- (A, b+2*k, 2, D, 0) →* (A+k, b, 2, D+k, 0)
theorem interleave_e0 : ∀ k, ⟨A, b + 2 * k, 2, D, 0⟩ [fm]⊢*
    ⟨A + k, b, 2, D + k, 0⟩ := by
  intro k; induction' k with k ih generalizing A b D
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (A := A) (b := b + 2) (D := D))
    rw [show b + 2 = b + 2 from rfl]
    exact stepPlus_stepStar (round_e0 (A := A + k) (b := b) (D := D + k))

-- One round with e=1.
theorem round_e1 : ⟨A, b + 2, 2, D, 1⟩ [fm]⊢⁺ ⟨A + 1, b, 2, D + 1, 1⟩ := by
  step fm; step fm; step fm; finish

-- Interleaved chain with e=1.
theorem interleave_e1 : ∀ k, ⟨A, b + 2 * k, 2, D, 1⟩ [fm]⊢*
    ⟨A + k, b, 2, D + k, 1⟩ := by
  intro k; induction' k with k ih generalizing A b D
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (A := A) (b := b + 2) (D := D))
    exact stepPlus_stepStar (round_e1 (A := A + k) (b := b) (D := D + k))

-- Opening with e=0: R5+R1+R3.
theorem opening_e0 : ⟨a + 1, b, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 1, b + 1, 2, 0, 0⟩ := by
  execute fm 3

-- Opening with e=1: R5+R1+R3.
theorem opening_e1 : ⟨a + 1, b, 0, 0, 1⟩ [fm]⊢⁺ ⟨a + 1, b + 1, 2, 0, 1⟩ := by
  execute fm 3

-- R3 chain with e=0.
theorem r3_chain_e0 : ∀ k, ⟨A, 0, C, D + k, 0⟩ [fm]⊢*
    ⟨A + k, 0, C + 2 * k, D, 0⟩ := by
  intro k; induction' k with k ih generalizing A C D
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A := A + 1) (C := C + 2))
    ring_nf; finish

-- R3 chain with e=1.
theorem r3_chain_e1 : ∀ k, ⟨A, 0, C, D + k, 1⟩ [fm]⊢*
    ⟨A + k, 0, C + 2 * k, D, 1⟩ := by
  intro k; induction' k with k ih generalizing A C D
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (A := A + 1) (C := C + 2))
    ring_nf; finish

-- R4 chain.
theorem r4_chain : ∀ k, ⟨A, 0, k, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih generalizing E
  · exists 0
  · step fm
    apply stepStar_trans (ih (E := E + 1))
    ring_nf; finish

-- Even transition: (a+3k+1, 0, 0, 0, 6k) →⁺ (a+6k+2, 0, 0, 0, 6k+3)
theorem even_trans : ⟨a + 3 * k + 1, 0, 0, 0, 6 * k⟩ [fm]⊢⁺
    ⟨a + 6 * k + 2, 0, 0, 0, 6 * k + 3⟩ := by
  -- Phase 1: drain 3k rounds.
  rw [show a + 3 * k + 1 = (a + 1) + 3 * k from by ring,
      show 6 * k = 2 * (3 * k) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_even (a := a + 1) (b := 0) (3 * k))
  rw [show 0 + 2 * (3 * k) = 6 * k from by ring]
  -- Phase 2: opening with e=0.
  apply stepPlus_stepStar_stepPlus (opening_e0 (a := a) (b := 6 * k))
  -- Now at (a+1, 6k+1, 2, 0, 0).
  -- Phase 3: interleave 3k rounds.
  rw [show 6 * k + 1 = 1 + 2 * (3 * k) from by ring]
  apply stepStar_trans (interleave_e0 (A := a + 1) (b := 1) (D := 0) (3 * k))
  -- Now at (a+3k+1, 1, 2, 3k, 0).
  -- Phase 4: R1 tail.
  rw [show 1 = 0 + 1 from by ring]
  step fm  -- R1: (a+3k+1, 0, 1, 3k+1, 0)
  -- Phase 5: R3 chain with 3k+1 steps.
  show ⟨a + 1 + 3 * k, 0, 1, 0 + 3 * k + 1, 0⟩ [fm]⊢* _
  rw [show 0 + 3 * k + 1 = 0 + (3 * k + 1) from by ring,
      show a + 1 + 3 * k = a + 3 * k + 1 from by ring]
  apply stepStar_trans (r3_chain_e0 (A := a + 3 * k + 1) (C := 1) (D := 0) (3 * k + 1))
  rw [show a + 3 * k + 1 + (3 * k + 1) = a + 6 * k + 2 from by ring,
      show 1 + 2 * (3 * k + 1) = 6 * k + 3 from by ring]
  -- Phase 6: R4 chain.
  apply stepStar_trans (r4_chain (A := a + 6 * k + 2) (E := 0) (6 * k + 3))
  ring_nf; finish

-- Odd transition: (a+3k+2, 0, 0, 0, 6k+3) →⁺ (a+6k+4, 0, 0, 0, 6k+6)
theorem odd_trans : ⟨a + 3 * k + 2, 0, 0, 0, 6 * k + 3⟩ [fm]⊢⁺
    ⟨a + 6 * k + 4, 0, 0, 0, 6 * k + 6⟩ := by
  -- Phase 1: drain 3k+1 rounds.
  rw [show a + 3 * k + 2 = (a + 1) + (3 * k + 1) from by ring,
      show 6 * k + 3 = 2 * (3 * k + 1) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (drain_odd (a := a + 1) (b := 0) (3 * k + 1))
  rw [show 0 + 2 * (3 * k + 1) = 6 * k + 2 from by ring]
  -- Phase 2: opening with e=1.
  apply stepPlus_stepStar_stepPlus (opening_e1 (a := a) (b := 6 * k + 2))
  -- Now at (a+1, 6k+3, 2, 0, 1).
  -- Phase 3: interleave 3k+1 rounds.
  rw [show 6 * k + 2 + 1 = 1 + 2 * (3 * k + 1) from by ring]
  apply stepStar_trans (interleave_e1 (A := a + 1) (b := 1) (D := 0) (3 * k + 1))
  -- Now at (a+3k+2, 1, 2, 3k+1, 1).
  -- Phase 4: R1 tail.
  rw [show 1 = 0 + 1 from by ring]
  step fm
  -- Phase 5: R3 chain with 3k+2 steps.
  show ⟨a + 1 + (3 * k + 1), 0, 1, 0 + (3 * k + 1) + 1, 1⟩ [fm]⊢* _
  rw [show 0 + (3 * k + 1) + 1 = 0 + (3 * k + 2) from by ring,
      show a + 1 + (3 * k + 1) = a + 3 * k + 2 from by ring]
  apply stepStar_trans (r3_chain_e1 (A := a + 3 * k + 2) (C := 1) (D := 0) (3 * k + 2))
  rw [show a + 3 * k + 2 + (3 * k + 2) = a + 6 * k + 4 from by ring,
      show 1 + 2 * (3 * k + 2) = 6 * k + 5 from by ring]
  -- Phase 6: R4 chain.
  apply stepStar_trans (r4_chain (A := a + 6 * k + 4) (E := 1) (6 * k + 5))
  ring_nf; finish

-- Full macro: (a+3k+1, 0, 0, 0, 6k) →⁺ (a+9k+4, 0, 0, 0, 6(k+1))
theorem macro_trans : ⟨a + 3 * k + 1, 0, 0, 0, 6 * k⟩ [fm]⊢⁺
    ⟨a + 9 * k + 4, 0, 0, 0, 6 * (k + 1)⟩ := by
  apply stepPlus_trans even_trans
  rw [show a + 6 * k + 2 = (a + 3 * k) + 3 * k + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (odd_trans (a := a + 3 * k) (k := k))
  rw [show a + 3 * k + 6 * k + 4 = a + 9 * k + 4 from by ring,
      show 6 * k + 6 = 6 * (k + 1) from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, k⟩ ↦ ⟨a + 3 * k + 1, 0, 0, 0, 6 * k⟩) ⟨0, 0⟩
  intro ⟨a, k⟩
  refine ⟨⟨a + 6 * k, k + 1⟩, ?_⟩
  show ⟨a + 3 * k + 1, 0, 0, 0, 6 * k⟩ [fm]⊢⁺
    ⟨(a + 6 * k) + 3 * (k + 1) + 1, 0, 0, 0, 6 * (k + 1)⟩
  rw [show (a + 6 * k) + 3 * (k + 1) + 1 = a + 9 * k + 4 from by ring]
  exact macro_trans

end Sz22_2003_unofficial_1469
