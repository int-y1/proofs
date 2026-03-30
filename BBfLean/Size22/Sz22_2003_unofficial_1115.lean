import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1115: [5/6, 4/35, 77/2, 9/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  1  1
 0  2  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1115

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Phase 1: R3 drains a into d and e.
theorem r3_drain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 1))
    ring_nf; finish

-- Phase 2: R4 drains d into b.
theorem r4_drain : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 2))
    ring_nf; finish

-- R3/R2 chain: each pair does a+=1, c-=1, e+=1.
theorem r3r2_chain : ∀ k, ∀ a c e, ⟨a + 1, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + 1 + k, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (e + 1))
    ring_nf; finish

-- Middle round: 5 steps per round.
theorem middle_round : ∀ k, ∀ b c e, ⟨0, b + 3 * k, c, 0, e + k⟩ [fm]⊢* ⟨0, b, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3 * k) + 1 + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R5
    step fm  -- R1
    step fm  -- R2
    step fm  -- R1
    step fm  -- R1
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    apply stepStar_trans (ih b (c + 2) e)
    ring_nf; finish

-- End case B=0: from (0, 0, c+1, 0, e+1) ->+ (c+3, 0, 0, 0, e+c)
theorem end_b0 : ⟨0, 0, c + 1, 0, e + 1⟩ [fm]⊢⁺ ⟨c + 3, 0, 0, 0, e + c⟩ := by
  step fm  -- R5: (1, 0, c+1, 1, e)
  step fm  -- R2: (3, 0, c, 0, e)
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show c = 0 + c from by ring]
  apply stepStar_trans (r3r2_chain c 2 0 e)
  ring_nf; finish

-- End case B=1: from (0, 1, c+1, 0, e+1) ->+ (c+3, 0, 0, 0, e+c+1)
theorem end_b1 : ⟨0, 1, c + 1, 0, e + 1⟩ [fm]⊢⁺ ⟨c + 3, 0, 0, 0, e + c + 1⟩ := by
  step fm  -- R5: (1, 1, c+1, 1, e)
  step fm  -- R1: (0, 0, c+2, 1, e)
  step fm  -- R2: (2, 0, c+1, 0, e)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show c + 1 = 0 + (c + 1) from by ring]
  apply stepStar_trans (r3r2_chain (c + 1) 1 0 e)
  ring_nf; finish

-- End case B=2: from (0, 2, c, 0, e+1) ->+ (c+2, 0, 0, 0, e+c+1)
theorem end_b2 : ⟨0, 2, c, 0, e + 1⟩ [fm]⊢⁺ ⟨c + 2, 0, 0, 0, e + c + 1⟩ := by
  step fm  -- R5: (1, 2, c, 1, e)
  step fm  -- R1: (0, 1, c+1, 1, e)
  step fm  -- R2: (2, 1, c, 0, e)
  step fm  -- R1: (1, 0, c+1, 0, e)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show c + 1 = 0 + (c + 1) from by ring]
  apply stepStar_trans (r3r2_chain (c + 1) 0 0 e)
  ring_nf; finish

-- Transition for a = 3m+1: (3m+1, 0, 0, 0, e) ->+ (4m+2, 0, 0, 0, e+5m+1)
theorem trans_mod1 (m : ℕ) : ⟨3 * m + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨4 * m + 2, 0, 0, 0, e + 5 * m + 1⟩ := by
  -- Phase 1: R3 drain
  rw [show 3 * m + 1 = 0 + (3 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_drain (3 * m + 1) (a := 0) (d := 0) (e := e))
  -- Phase 2: R4 drain
  rw [show (0 : ℕ) = 0 from rfl,
      show 0 + (3 * m + 1) = 0 + (3 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (3 * m + 1) (b := 0) (d := 0) (e := e + (3 * m + 1)))
  -- Middle rounds: 2m rounds
  rw [show 0 + 2 * (3 * m + 1) = 2 + 3 * (2 * m) from by ring,
      show e + (3 * m + 1) = (e + m + 1) + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (middle_round (2 * m) 2 0 (e + m + 1))
  -- End case B=2
  rw [show 0 + 2 * (2 * m) = 4 * m from by ring,
      show e + m + 1 = e + m + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (end_b2 (c := 4 * m) (e := e + m))
  ring_nf; finish

-- Transition for a = 3m+2: (3m+2, 0, 0, 0, e) ->+ (4m+4, 0, 0, 0, e+5m+2)
theorem trans_mod2 (m : ℕ) : ⟨3 * m + 2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨4 * m + 4, 0, 0, 0, e + 5 * m + 2⟩ := by
  rw [show 3 * m + 2 = 0 + (3 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_drain (3 * m + 2) (a := 0) (d := 0) (e := e))
  rw [show (0 : ℕ) = 0 from rfl,
      show 0 + (3 * m + 2) = 0 + (3 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (3 * m + 2) (b := 0) (d := 0) (e := e + (3 * m + 2)))
  rw [show 0 + 2 * (3 * m + 2) = 1 + 3 * (2 * m + 1) from by ring,
      show e + (3 * m + 2) = (e + m + 1) + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (middle_round (2 * m + 1) 1 0 (e + m + 1))
  rw [show 0 + 2 * (2 * m + 1) = (4 * m + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (end_b1 (c := 4 * m + 1) (e := e + m))
  ring_nf; finish

-- Transition for a = 3(m+1): (3m+3, 0, 0, 0, e) ->+ (4m+6, 0, 0, 0, e+5m+3)
theorem trans_mod0 (m : ℕ) : ⟨3 * m + 3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨4 * m + 6, 0, 0, 0, e + 5 * m + 3⟩ := by
  rw [show 3 * m + 3 = 0 + (3 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_drain (3 * m + 3) (a := 0) (d := 0) (e := e))
  rw [show (0 : ℕ) = 0 from rfl,
      show 0 + (3 * m + 3) = 0 + (3 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain (3 * m + 3) (b := 0) (d := 0) (e := e + (3 * m + 3)))
  rw [show 0 + 2 * (3 * m + 3) = 0 + 3 * (2 * m + 2) from by ring,
      show e + (3 * m + 3) = (e + m + 1) + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (middle_round (2 * m + 2) 0 0 (e + m + 1))
  rw [show 0 + 2 * (2 * m + 2) = (4 * m + 3) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (end_b0 (c := 4 * m + 3) (e := e + m))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · exists 0
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, a = 3 * m ∨ a = 3 * m + 1 ∨ a = 3 * m + 2 :=
      ⟨a / 3, by omega⟩
    · exact ⟨⟨4 * m + 2, 0, 0, 0, e + 5 * m + 1⟩,
        ⟨4 * m + 1, e + 5 * m + 1, by ring_nf⟩,
        trans_mod1 m⟩
    · exact ⟨⟨4 * m + 4, 0, 0, 0, e + 5 * m + 2⟩,
        ⟨4 * m + 3, e + 5 * m + 2, by ring_nf⟩,
        trans_mod2 m⟩
    · exact ⟨⟨4 * m + 6, 0, 0, 0, e + 5 * m + 3⟩,
        ⟨4 * m + 5, e + 5 * m + 3, by ring_nf⟩,
        trans_mod0 m⟩
  · exact ⟨0, 0, rfl⟩
