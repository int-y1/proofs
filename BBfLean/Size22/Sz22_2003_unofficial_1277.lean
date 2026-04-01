import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1277: [56/15, 1/6, 9/7, 125/2, 7/5]

Vector representation:
```
 3 -1 -1  1
-1 -1  0  0
 0  2  0 -1
-1  0  3  0
 0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1277

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+3, b, c, d+1⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+2, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- R4 chain: convert a to c (b=0, d=0)
theorem r4_chain : ∀ k, ⟨k, (0 : ℕ), c, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + 3 * k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c := c + 3))
    ring_nf; finish

-- Bootstrap: (0, 0, c+3, 0) ->* (6, 0, c, 2)
theorem bootstrap : ⟨(0 : ℕ), (0 : ℕ), c + 3, (0 : ℕ)⟩ [fm]⊢* ⟨6, (0 : ℕ), c, 2⟩ := by
  rw [show c + 3 = (c + 2) + 1 from by ring]
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm
  step fm
  step fm
  ring_nf; finish

-- Spiral round: (a, 0, c+2, d+1) ->* (a+6, 0, c, d+2)
theorem spiral_round (a c d : ℕ) :
    ⟨a, (0 : ℕ), c + 2, d + 1⟩ [fm]⊢* ⟨a + 6, (0 : ℕ), c, d + 2⟩ := by
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm
  step fm
  ring_nf; finish

-- Spiral chain: k rounds
theorem spiral : ∀ k, ∀ a c d, ⟨a, (0 : ℕ), c + 2 * k, d + 1⟩ [fm]⊢* ⟨a + 6 * k, (0 : ℕ), c, d + k + 1⟩ := by
  intro k; induction' k with k ih
  · intro a c d; simp; exists 0
  · intro a c d
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    apply stepStar_trans (ih a (c + 2) d)
    rw [show d + k + 1 = (d + k) + 1 from by ring]
    apply stepStar_trans (spiral_round (a + 6 * k) c (d + k))
    ring_nf; finish

-- c=1 ending: (a, 0, 1, d+1) ->* (a+2, 0, 0, d+1)
theorem c1_ending (a d : ℕ) :
    ⟨a, (0 : ℕ), 1, d + 1⟩ [fm]⊢* ⟨a + 2, (0 : ℕ), (0 : ℕ), d + 1⟩ := by
  step fm
  step fm
  step fm
  ring_nf; finish

-- R3-R2-R2 drain: one round (a+2, 0, 0, d+1) ->* (a, 0, 0, d)
theorem drain_round (a d : ℕ) :
    ⟨a + 2, (0 : ℕ), (0 : ℕ), d + 1⟩ [fm]⊢* ⟨a, (0 : ℕ), (0 : ℕ), d⟩ := by
  step fm
  step fm
  step fm
  finish

-- Drain chain: k rounds
theorem drain_chain : ∀ k, ∀ a, ⟨a + 2 * k, (0 : ℕ), (0 : ℕ), k⟩ [fm]⊢* ⟨a, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ := by
  intro k; induction' k with k ih
  · intro a; simp; exists 0
  · intro a
    rw [show a + 2 * (k + 1) = a + 2 * k + 2 from by ring]
    apply stepStar_trans (drain_round (a + 2 * k) k)
    exact ih a

-- Full transition for even index: (2m+1, 0, 0, 0) ⊢⁺ (12m+2, 0, 0, 0)
theorem main_trans_even (m : ℕ) :
    ⟨2 * m + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺
    ⟨12 * m + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ := by
  -- Phase 1: First R4 step (for ⊢⁺)
  step fm
  -- State: (2m, 0, 3, 0)
  -- Remaining R4 chain
  apply stepStar_trans
  · rw [show (3 : ℕ) = 3 + 3 * 0 from by ring]
    exact r4_chain (2 * m)
  rw [show 3 + 3 * (2 * m) = 6 * m + 3 from by ring]
  -- Phase 2: Bootstrap
  apply stepStar_trans
  · rw [show 6 * m + 3 = (6 * m) + 3 from by ring]
    exact bootstrap (c := 6 * m)
  -- State: (6, 0, 6m, 2)
  -- Phase 3: Spiral with k = 3m
  apply stepStar_trans
  · rw [show 6 * m = 0 + 2 * (3 * m) from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    exact spiral (3 * m) 6 0 1
  rw [show 6 + 6 * (3 * m) = 18 * m + 6 from by ring,
      show 1 + 3 * m + 1 = 3 * m + 2 from by ring]
  -- State: (18m+6, 0, 0, 3m+2)
  -- Phase 4: Drain with k = 3m+2
  rw [show 18 * m + 6 = (12 * m + 2) + 2 * (3 * m + 2) from by ring]
  exact drain_chain (3 * m + 2) (12 * m + 2)

-- Full transition for odd index: (2m+2, 0, 0, 0) ⊢⁺ (12m+8, 0, 0, 0)
theorem main_trans_odd (m : ℕ) :
    ⟨2 * m + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺
    ⟨12 * m + 8, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ := by
  -- Phase 1: First R4 step (for ⊢⁺)
  step fm
  -- State: (2m+1, 0, 3, 0)
  -- Remaining R4 chain
  apply stepStar_trans
  · rw [show (3 : ℕ) = 3 + 3 * 0 from by ring]
    exact r4_chain (2 * m + 1)
  rw [show 3 + 3 * (2 * m + 1) = 6 * m + 6 from by ring]
  -- Phase 2: Bootstrap
  apply stepStar_trans
  · rw [show 6 * m + 6 = (6 * m + 3) + 3 from by ring]
    exact bootstrap (c := 6 * m + 3)
  -- State: (6, 0, 6m+3, 2)
  -- Phase 3: Spiral with k = 3m+1 (leaves c = 1)
  apply stepStar_trans
  · rw [show 6 * m + 3 = 1 + 2 * (3 * m + 1) from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    exact spiral (3 * m + 1) 6 1 1
  rw [show 6 + 6 * (3 * m + 1) = 18 * m + 12 from by ring,
      show 1 + (3 * m + 1) + 1 = 3 * m + 3 from by ring]
  -- State: (18m+12, 0, 1, 3m+3)
  -- Phase 3b: c=1 ending
  apply stepStar_trans
  · rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring]
    exact c1_ending (18 * m + 12) (3 * m + 2)
  rw [show 18 * m + 12 + 2 = 18 * m + 14 from by ring,
      show 3 * m + 2 + 1 = 3 * m + 3 from by ring]
  -- State: (18m+14, 0, 0, 3m+3)
  -- Phase 4: Drain with k = 3m+3
  rw [show 18 * m + 14 = (12 * m + 8) + 2 * (3 * m + 3) from by ring]
  exact drain_chain (3 * m + 3) (12 * m + 8)

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun a ↦ ⟨a + 1, 0, 0, 0⟩) 0
  intro a
  rcases Nat.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exists 12 * m + 1
    show ⟨2 * m + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺ ⟨12 * m + 1 + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩
    rw [show 12 * m + 1 + 1 = 12 * m + 2 from by ring]
    exact main_trans_even m
  · subst hm
    exists 12 * m + 7
    show ⟨2 * m + 1 + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺ ⟨12 * m + 7 + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show 12 * m + 7 + 1 = 12 * m + 8 from by ring]
    exact main_trans_odd m

end Sz22_2003_unofficial_1277
