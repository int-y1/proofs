import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1479: [7/15, 44/3, 1089/14, 5/11, 3/2]

Vector representation:
```
 0 -1 -1  1  0
 2 -1  0  0  1
-1  2  0 -1  2
 0  0  1  0 -1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1479

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- Phase 1: R4 chain — transfer e to c.
theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih (c := c + 1) (e := e)); ring_nf; finish

-- Phase 2: R3/R1/R1 chain — each round drains c by 2 and a by 1.
theorem r3r1r1_chain : ∀ k, ∀ a c d e,
    ⟨a + k + 1, 0, c + 2 * k, d + 1, e⟩ [fm]⊢* ⟨a + 1, 0, c, d + k + 1, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
    step fm  -- R3
    step fm  -- R1
    step fm  -- R1
    apply stepStar_trans (ih a c (d + 1) (e + 2)); ring_nf; finish

-- Phase 3: R3/R2/R2 chain — drains d.
theorem r3r2r2_chain : ∀ k, ∀ a d e,
    ⟨a + 1, 0, 0, d + k, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, d, e + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    step fm  -- R2
    apply stepStar_trans (ih (a + 3) d (e + 4)); ring_nf; finish

-- Tail for c=1 remainder: (A+1, 0, 1, D+1, E) -> (A+2, 0, 0, D+1, E+3).
theorem tail_c1 : ⟨a + 1, 0, 1, d + 1, e⟩ [fm]⊢* ⟨a + 2, 0, 0, d + 1, e + 3⟩ := by
  step fm  -- R3
  step fm  -- R1
  step fm  -- R2
  ring_nf; finish

-- Main transition for e=0: (a+2, 0, 0, 0, 0) ⊢⁺ (a+3, 0, 0, 0, 1).
theorem trans_e0 (a : ℕ) : ⟨a + 2, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 0, 1⟩ := by
  step fm  -- R5
  step fm  -- R2
  ring_nf; finish

-- Main transition for odd e: (a, 0, 0, 0, 2k+1) ⊢⁺ (a+2k+2, 0, 0, 0, 6k+4).
-- Requires a ≥ k+2.
theorem trans_odd (a k : ℕ) :
    ⟨a + k + 2, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨a + 3 * k + 4, 0, 0, 0, 6 * k + 4⟩ := by
  -- Phase 1: e_to_c
  rw [show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * k + 1) (a := a + k + 2) (c := 0) (e := 0))
  -- Now: (a+k+2, 0, 2k+1, 0, 0)
  -- Phase 2a: opening R5/R1
  rw [show (0 + (2 * k + 1) : ℕ) = (2 * k) + 1 from by ring,
      show (a + k + 2 : ℕ) = (a + k + 1) + 1 from by ring]
  step fm  -- R5
  step fm  -- R1
  -- Now: (a+k+1, 0, 2k, 1, 0)
  -- Phase 2b: r3r1r1 x k
  rw [show (a + k + 1 : ℕ) = a + k + 1 from by ring,
      show (2 * k : ℕ) = 0 + 2 * k from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain k a 0 0 0)
  -- Now: (a+1, 0, 0, k+1, 2k)
  rw [show (0 + k + 1 : ℕ) = k + 1 from by ring,
      show (0 + 2 * k : ℕ) = 2 * k from by ring,
      show (a + 1 : ℕ) = a + 1 from by ring,
      show (k + 1 : ℕ) = 0 + (k + 1) from by ring]
  -- Phase 3: r3r2r2 x (k+1)
  apply stepStar_trans (r3r2r2_chain (k + 1) a 0 (2 * k))
  ring_nf; finish

-- Main transition for even e: (a, 0, 0, 0, 2k+2) ⊢⁺ (a+2k+3, 0, 0, 0, 6k+7).
-- Requires a ≥ k+3.
theorem trans_even (a k : ℕ) :
    ⟨a + k + 3, 0, 0, 0, 2 * k + 2⟩ [fm]⊢⁺ ⟨a + 3 * k + 6, 0, 0, 0, 6 * k + 7⟩ := by
  -- Phase 1: e_to_c
  rw [show (2 * k + 2 : ℕ) = 0 + (2 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (2 * k + 2) (a := a + k + 3) (c := 0) (e := 0))
  -- Now: (a+k+3, 0, 2k+2, 0, 0)
  -- Phase 2a: opening R5/R1
  rw [show (0 + (2 * k + 2) : ℕ) = (2 * k + 1) + 1 from by ring,
      show (a + k + 3 : ℕ) = (a + k + 2) + 1 from by ring]
  step fm  -- R5
  step fm  -- R1
  -- Now: (a+k+2, 0, 2k+1, 1, 0)
  -- Phase 2b: r3r1r1 x k
  rw [show (a + k + 2 : ℕ) = (a + 1) + k + 1 from by ring,
      show (2 * k + 1 : ℕ) = 1 + 2 * k from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain k (a + 1) 1 0 0)
  -- Now: (a+2, 0, 1, k+1, 2k)
  rw [show (a + 1 + 1 : ℕ) = (a + 1) + 1 from by ring,
      show (0 + k + 1 : ℕ) = k + 1 from by ring,
      show (0 + 2 * k : ℕ) = 2 * k from by ring]
  -- Phase 2c: tail_c1
  apply stepStar_trans (tail_c1 (a := a + 1) (d := k) (e := 2 * k))
  -- Now: (a+3, 0, 0, k+1, 2k+3)
  -- Phase 3: r3r2r2 x (k+1)
  rw [show (a + 1 + 2 : ℕ) = a + 2 + 1 from by ring,
      show (k + 1 : ℕ) = 0 + (k + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 1) (a + 2) 0 (2 * k + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ 2 * a ≥ e + 3)
  · intro c ⟨a, e, hq, hinv⟩; subst hq
    rcases e with _ | e
    · -- e = 0
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 := ⟨a - 2, by omega⟩
      exact ⟨⟨F + 3, 0, 0, 0, 1⟩, ⟨F + 3, 1, rfl, by omega⟩, trans_e0 F⟩
    · rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- e+1 = 2k+1 (odd), so e = 2k
        rw [show k + k = 2 * k from by ring] at hk; subst hk
        obtain ⟨F, rfl⟩ : ∃ F, a = F + k + 2 := ⟨a - k - 2, by omega⟩
        exact ⟨⟨F + 3 * k + 4, 0, 0, 0, 6 * k + 4⟩,
               ⟨F + 3 * k + 4, 6 * k + 4, rfl, by omega⟩, trans_odd F k⟩
      · -- e+1 = 2k+2 (even), so e = 2k+1
        subst hk
        obtain ⟨F, rfl⟩ : ∃ F, a = F + k + 3 := ⟨a - k - 3, by omega⟩
        exact ⟨⟨F + 3 * k + 6, 0, 0, 0, 6 * k + 7⟩,
               ⟨F + 3 * k + 6, 6 * k + 7, rfl, by omega⟩, trans_even F k⟩
  · exact ⟨2, 1, rfl, by omega⟩

end Sz22_2003_unofficial_1479
