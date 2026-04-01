import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1454: [7/15, 3/14, 275/7, 4/55, 21/2]

Vector representation:
```
 0 -1 -1  1  0
-1  1  0 -1  0
 0  0  2 -1  1
 2  0 -1  0 -1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1454

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R5,R2 interleaving: drain a into b in pairs.
theorem r5r2_drain : ∀ k, ⟨a + 1 + 2 * k, b, 0, 0, 0⟩ [fm]⊢* ⟨a + 1, b + 2 * k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show a + 1 + 2 * (k + 1) = (a + 1 + 2 * k) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a) (b := b + 2))
    ring_nf; finish

-- One round of R1,R1,R3: (0, b+2, 2, d, e) -> (0, b, 2, d+1, e+1)
-- This fires: R1 (b+2 = (b+1)+1, c = 2 = 1+1), R1 (b+1 = b+1, c = 1 = 0+1), R3 (d+2 = (d+1)+1).
-- After R1: (0, b+1, 1, d+1, e). After R1: (0, b, 0, d+2, e). After R3: (0, b, 2, d+1, e+1).
theorem r1r1r3_round : ⟨0, b + 1 + 1, 1 + 1, d, e⟩ [fm]⊢* ⟨0, b, 2, d + 1, e + 1⟩ := by
  step fm  -- R1: (0, b+1, 1, d+1, e) = (0, b+1, 0+1, d+1, e)
  step fm  -- R1: (0, b, 0, d+1+1, e)
  step fm  -- R3: (0, b, 2, d+1, e+1)
  ring_nf; finish

-- Chain of R1,R1,R3 rounds.
theorem r1r1r3_chain : ∀ k, ∀ b d e,
    ⟨0, b + 2 * k, 2, d, e⟩ [fm]⊢* ⟨0, b, 2, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (r1r1r3_round (b := b + 2 * k) (d := d) (e := e))
    apply stepStar_trans (ih b (d + 1) (e + 1))
    ring_nf; finish

-- R3 chain: (0, 0, c, d+k, e) ->* (0, 0, c+2k, d, e+k).
-- a=0 so R2 doesn't fire. b=0 so R1 doesn't fire. R3 fires.
theorem r3_chain : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [Nat.add_succ d k]
    step fm  -- R3
    apply stepStar_trans (ih (c := c + 2) (d := d) (e := e + 1))
    ring_nf; finish

-- R4 chain: (a, 0, c+k, 0, e+k) ->* (a+2k, 0, c, 0, e).
-- b=0, d=0. R1 fails (b=0). R2 fails (d=0). R3 fails (d=0). R4 fires (c>=1, e>=1).
theorem r4_chain : ∀ k, ⟨a, 0, c + k, 0, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm  -- R4
    apply stepStar_trans (ih (a := a + 2) (c := c) (e := e))
    ring_nf; finish

-- Full phase: (2n+3, 0, 0, 2, 0) ⊢⁺ (4n+7, 0, 0, 2, 0)
theorem main_trans : ⟨2 * n + 3, 0, 0, 2, 0⟩ [fm]⊢⁺ ⟨4 * n + 7, 0, 0, 2, 0⟩ := by
  -- R2, R2: (2n+3, 0, 0, 2, 0) -> (2n+1, 2, 0, 0, 0)
  step fm; step fm
  -- R5,R2 drain: (2n+1, 2, 0, 0, 0) -> (1, 2n+2, 0, 0, 0)
  rw [show 2 * n + 1 = 0 + 1 + 2 * n from by ring]
  apply stepStar_trans (r5r2_drain n (a := 0) (b := 2))
  -- Now at (0+1, 2+2n, 0, 0, 0) = (1, 2n+2, 0, 0, 0)
  -- R5: (1, 2n+2, 0, 0, 0) -> (0, 2n+3, 0, 1, 0)
  rw [show (0 : ℕ) + 1 = 1 from by ring, show 2 + 2 * n = 2 * n + 2 from by ring]
  step fm
  -- R3: (0, 2n+3, 0, 1, 0) -> (0, 2n+3, 2, 0, 1)
  step fm
  -- R1,R1,R3 chain: (0, 1+2(n+1), 2, 0, 1) -> (0, 1, 2, n+1, n+2)
  rw [show 2 * n + 3 = 1 + 2 * (n + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (n + 1) 1 0 1)
  -- At (0, 1, 2, n+1, n+2). R1: (0, 0, 1, n+2, n+2)
  rw [show (0 : ℕ) + (n + 1) = n + 1 from by ring, show 1 + (n + 1) = n + 2 from by ring]
  step fm
  -- R3 chain: (0, 0, 1, n+2, n+2) -> (0, 0, 2n+5, 0, 2n+4)
  rw [show n + 1 + 1 = n + 2 from by ring]
  rw [show (n : ℕ) + 2 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r3_chain (n + 2) (c := 1) (d := 0) (e := 0 + (n + 2)))
  -- R4 chain: (0, 0, 2n+5, 0, 2n+4) -> (4n+8, 0, 1, 0, 0)
  rw [show 0 + (n + 2) + (n + 2) = 0 + (2 * n + 4) from by ring]
  apply stepStar_trans (r4_chain (2 * n + 4) (a := 0) (c := 1) (e := 0))
  -- R5: (4n+8, 0, 1, 0, 0) -> (4n+7, 1, 1, 1, 0)
  rw [show 0 + 2 * (2 * n + 4) = 4 * n + 8 from by ring]
  step fm
  -- R1: (4n+7, 1, 1, 1, 0) -> (4n+7, 0, 0, 2, 0)
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 2, 0⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, 2, 0⟩) 0
  intro n; exists 2 * n + 2
  show ⟨2 * n + 3, 0, 0, 2, 0⟩ [fm]⊢⁺ ⟨2 * (2 * n + 2) + 3, 0, 0, 2, 0⟩
  rw [show 2 * (2 * n + 2) + 3 = 4 * n + 7 from by ring]
  exact main_trans
