import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1088: [5/6, 2/385, 49/2, 33/7, 20/3]

Vector representation:
```
-1 -1  1  0  0
 1  0 -1 -1 -1
-1  0  0  2  0
 0  1  0 -1  1
 2 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1088

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

-- R3 chain: (a, 0, 0, d, 0) ->* (0, 0, 0, d + 2*a, 0)
theorem r3_chain : ∀ a, ⟨a, 0, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * a, 0⟩ := by
  intro a; induction' a with a ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

-- R4 chain: (0, b, 0, k + d, e) ->* (0, b + k, 0, d, e + k)
theorem r4_chain : ∀ k, ⟨0, b, 0, k + d, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · simp; exists 0
  · rw [show k + 1 + d = k + (d + 1) from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d) (e := e + 1))
    ring_nf; finish

-- R5+R1+R1 chain: each round transfers 3 from b to c
theorem r5r1r1_chain : ∀ k, ∀ b c, ⟨0, b + 3 * k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3 * k) + 1 + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 3))
    ring_nf; finish

-- R3+R2+R2 drain: each round drains 2 from c,e and adds 1 to a
theorem drain : ∀ k, ⟨a + 1, 0, c + 2 * k, 0, e + 2 * k⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

-- R5+R1 tail: handles b=2 remainder
theorem r5r1_tail : ⟨0, 2, c, 0, e⟩ [fm]⊢* ⟨1, 0, c + 2, 0, e⟩ := by
  step fm; step fm; finish

-- R5 tail: handles b=1 remainder
theorem r5_tail : ⟨0, 1, c, 0, e⟩ [fm]⊢* ⟨2, 0, c + 1, 0, e⟩ := by
  step fm; finish

-- Transition for a = 3*k+1: (3*k+1, 0, 0, 0, 0) ⊢⁺ (3*k+2, 0, 0, 0, 0)
-- 2a = 6k+2, 2a mod 3 = 2. R5R1R1 chain has 2k rounds, remainder 2.
-- After R5R1 tail: (1, 0, 6k+2, 0, 6k+2). Drain with 3k+1 rounds: (3k+2, 0, 0, 0, 0).
theorem trans_mod1 (k : ℕ) : ⟨3 * k + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨3 * k + 2, 0, 0, 0, 0⟩ := by
  -- R3 chain: first step gives ⊢⁺
  apply step_stepStar_stepPlus (by simp [fm] : ⟨3 * k + 1, 0, 0, 0, 0⟩ [fm]⊢ ⟨3 * k, 0, 0, 2, 0⟩)
  -- rest of R3 chain
  apply stepStar_trans (r3_chain (3 * k) (d := 2))
  -- R4 chain
  rw [show 2 + 2 * (3 * k) = (6 * k + 2) + 0 from by ring]
  apply stepStar_trans (r4_chain (6 * k + 2) (b := 0) (d := 0) (e := 0))
  -- R5R1R1 chain
  rw [show 0 + (6 * k + 2) = 2 + 3 * (2 * k) from by ring]
  apply stepStar_trans (r5r1r1_chain (2 * k) 2 0 (e := 2 + 3 * (2 * k)))
  -- R5+R1 tail
  apply stepStar_trans (r5r1_tail (c := 0 + 3 * (2 * k)) (e := 2 + 3 * (2 * k)))
  -- drain
  rw [show 0 + 3 * (2 * k) + 2 = 0 + 2 * (3 * k + 1) from by ring,
      show 2 + 3 * (2 * k) = 0 + 2 * (3 * k + 1) from by ring]
  apply stepStar_trans (drain (3 * k + 1) (a := 0) (c := 0) (e := 0))
  rw [show 0 + (3 * k + 1) + 1 = 3 * k + 2 from by ring]
  finish

-- Transition for a = 3*k+2: (3*k+2, 0, 0, 0, 0) ⊢⁺ (3*(k+1)+1, 0, 0, 0, 0)
-- 2a = 6k+4, 2a mod 3 = 1. R5R1R1 chain has 2k+1 rounds, remainder 1.
-- After R5 tail: (2, 0, 6k+4, 0, 6k+4). Drain with 3k+2 rounds: (3k+4, 0, 0, 0, 0).
theorem trans_mod2 (k : ℕ) : ⟨3 * k + 2, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨3 * (k + 1) + 1, 0, 0, 0, 0⟩ := by
  -- R3 chain: first step gives ⊢⁺
  apply step_stepStar_stepPlus (by simp [fm] : ⟨3 * k + 2, 0, 0, 0, 0⟩ [fm]⊢ ⟨3 * k + 1, 0, 0, 2, 0⟩)
  -- rest of R3 chain
  apply stepStar_trans (r3_chain (3 * k + 1) (d := 2))
  -- R4 chain
  rw [show 2 + 2 * (3 * k + 1) = (6 * k + 4) + 0 from by ring]
  apply stepStar_trans (r4_chain (6 * k + 4) (b := 0) (d := 0) (e := 0))
  -- R5R1R1 chain
  rw [show 0 + (6 * k + 4) = 1 + 3 * (2 * k + 1) from by ring]
  apply stepStar_trans (r5r1r1_chain (2 * k + 1) 1 0 (e := 1 + 3 * (2 * k + 1)))
  -- R5 tail
  apply stepStar_trans (r5_tail (c := 0 + 3 * (2 * k + 1)) (e := 1 + 3 * (2 * k + 1)))
  -- drain
  rw [show 0 + 3 * (2 * k + 1) + 1 = 0 + 2 * (3 * k + 2) from by ring,
      show 1 + 3 * (2 * k + 1) = 0 + 2 * (3 * k + 2) from by ring]
  apply stepStar_trans (drain (3 * k + 2) (a := 1) (c := 0) (e := 0))
  rw [show 1 + (3 * k + 2) + 1 = 3 * (k + 1) + 1 from by ring]
  finish

-- Combined: (3*k+1, 0, 0, 0, 0) ⊢⁺ (3*(k+1)+1, 0, 0, 0, 0)
theorem main_trans (k : ℕ) : ⟨3 * k + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨3 * (k + 1) + 1, 0, 0, 0, 0⟩ :=
  stepPlus_trans (trans_mod1 k) (trans_mod2 k)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨3 * k + 1, 0, 0, 0, 0⟩) 0
  intro k; exact ⟨k + 1, main_trans k⟩

end Sz22_2003_unofficial_1088
