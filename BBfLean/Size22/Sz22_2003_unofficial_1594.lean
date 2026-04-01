import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1594: [77/15, 1/3, 12/7, 25/2, 1/55, 3/5]

Vector representation:
```
 0 -1 -1  1  1
 0 -1  0  0  0
 2  1  0 -1  0
-1  0  2  0  0
 0  0 -1  0 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1594

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R1/R3 interleaved chain: each round does R1 then R3
-- (a, 1, c+k, 0, e) ⊢* (a+2k, 1, c, 0, e+k)
-- but we need b=1 and d=0. After R1: b=0,c-1,d=1,e+1. After R3: a+2,b=1,d=0,e+1.
theorem r1r3_chain : ∀ k, ∀ a c e, ⟨a, 1, c + k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 1, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) c (e + 1)); ring_nf; finish

-- R4 drain: (a, 0, c, 0, e) ⊢* (0, 0, c+2a, 0, e)
theorem r4_drain : ∀ a, ∀ c e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * a, 0, e⟩ := by
  intro a; induction' a with a ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 2) e); ring_nf; finish

-- R5 drain: (0, 0, c+e, 0, e) ⊢* (0, 0, c, 0, 0)
theorem r5_drain : ∀ e, ∀ c, ⟨0, 0, c + e, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, 0⟩ := by
  intro e; induction' e with e ih <;> intro c
  · exists 0
  · rw [show c + (e + 1) = (c + e) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c); finish

-- Main transition: (0, 0, n+2, 0, 0) ⊢⁺ (0, 0, 3n+3, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 0, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * n + 3, 0, 0⟩ := by
  -- Phase 1: R6: (0, 0, n+2, 0, 0) -> (0, 1, n+1, 0, 0)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- Phase 2: R1/R3 chain (n+1 rounds): (0, 1, n+1, 0, 0) -> (2(n+1), 1, 0, 0, n+1)
  rw [show (n + 1 : ℕ) = 0 + (n + 1) from by ring]
  apply stepStar_trans (r1r3_chain (n + 1) 0 0 0)
  rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring,
      show (0 + (n + 1) : ℕ) = n + 1 from by ring]
  -- Phase 2b: R2: (2n+2, 1, 0, 0, n+1) -> (2n+2, 0, 0, 0, n+1)
  step fm
  -- Phase 3: R4 drain: (2n+2, 0, 0, 0, n+1) -> (0, 0, 2(2n+2), 0, n+1) = (0, 0, 4n+4, 0, n+1)
  apply stepStar_trans (r4_drain (2 * n + 2) 0 (n + 1))
  rw [show 0 + 2 * (2 * n + 2) = 4 * n + 4 from by ring]
  -- Phase 4: R5 drain: (0, 0, 4n+4, 0, n+1) -> (0, 0, 3n+3, 0, 0)
  rw [show 4 * n + 4 = (3 * n + 3) + (n + 1) from by ring]
  apply stepStar_trans (r5_drain (n + 1) (3 * n + 3))
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 0, 0⟩) 0
  intro n; exact ⟨3 * n + 1, main_trans n⟩

end Sz22_2003_unofficial_1594
