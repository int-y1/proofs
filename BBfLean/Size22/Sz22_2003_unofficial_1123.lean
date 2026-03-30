import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1123: [5/6, 44/245, 49/2, 3/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -2  1
-1  0  0  2  0
 0  1  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1123

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+2, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R3 chain: drain a into d (each step: a -= 1, d += 2), with b = 0, c = 0.
theorem r3_chain : ∀ a, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * a, e⟩ := by
  intro a; induction' a with a ih generalizing d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d := d + 2))
    ring_nf; finish

-- R4 chain: drain e into b (each step: e -= 1, b += 1), with a = 0, c = 0.
theorem r4_chain : ∀ e, ⟨0, b, 0, d, e⟩ [fm]⊢* ⟨0, b + e, 0, d, 0⟩ := by
  intro e; induction' e with e ih generalizing b
  · exists 0
  · step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R1,R1,R2 chain: each round does R1 twice then R2 once.
-- Net per round: b -= 2, d -= 2, c += 1, e += 1, a stays 2.
theorem r1r1r2_chain : ∀ k, ⟨2, B + 2 * k, C, D + 2 * k, E⟩ [fm]⊢*
    ⟨2, B, C + k, D, E + k⟩ := by
  intro k; induction' k with k ih generalizing B C D E
  · exists 0
  · rw [show B + 2 * (k + 1) = (B + 2) + 2 * k from by ring,
        show D + 2 * (k + 1) = (D + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (B := B + 2) (D := D + 2))
    step fm; step fm; step fm
    ring_nf; finish

-- R3,R2 chain with d = 1: each round does R3 then R2.
-- Net per round: a += 1, c -= 1, e += 1, d stays 1.
theorem r3_r2_d1 : ∀ k, ⟨a + 1, 0, k, 1, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 1, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

-- R3,R2 chain with d = 0: each round does R3 then R2.
-- Net per round: a += 1, c -= 1, e += 1, d stays 0.
theorem r3_r2_d0 : ∀ k, ⟨a + 1, 0, k, 0, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

-- Process even: from (0, 2k, 0, 2k+2, 0) reach (k+1, 0, 0, 1, 2k+1).
-- This handles the interleave phase when B = D - 2 and D is even.
theorem process_even : ∀ k, ⟨0, 2 * k, 0, 2 * k + 2, 0⟩ [fm]⊢*
    ⟨k + 1, 0, 0, 1, 2 * k + 1⟩ := by
  intro k; induction' k with k ih
  · -- k = 0: (0, 0, 0, 2, 0) →* (1, 0, 0, 1, 1). One R5 step.
    step fm; finish
  · -- k+1: (0, 2k+2, 0, 2k+4, 0) →* (k+2, 0, 0, 1, 2k+3)
    -- Phase 1: R5, R1, R2 (3 steps)
    step fm; step fm; step fm
    -- Now at (2, 2k+1, 0, 2k+1, 2)
    -- Phase 2: r1r1r2_chain k rounds → (2, 1, k, 1, k+2)
    show ⟨2, 2 * k + 1, 0, 2 * k + 1, 2⟩ [fm]⊢* ⟨k + 1 + 1, 0, 0, 1, 2 * (k + 1) + 1⟩
    rw [show 2 * k + 1 = 1 + 2 * k from by ring,
        show (2 : ℕ) = 2 from rfl]
    apply stepStar_trans (r1r1r2_chain k (B := 1) (C := 0) (D := 1) (E := 2))
    -- Now at (2, 1, k, 1, k+2)
    -- Phase 3: R1, R3, R2 (3 steps) → (2, 0, k, 1, k+3)
    step fm; step fm; step fm
    -- Phase 4: r3_r2_d1 k rounds → (k+2, 0, 0, 1, 2k+3)
    rw [show (0 : ℕ) + k = k from by ring,
        show 2 + k + 1 = k + 3 from by ring]
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    apply stepStar_trans (r3_r2_d1 k (a := 1) (e := k + 3))
    ring_nf; finish

-- Process odd: from (0, 2k+1, 0, 2k+3, 0) reach (k+2, 0, 0, 0, 2k+2).
-- This handles the interleave phase when B = D - 2 and D is odd.
theorem process_odd : ∀ k, ⟨0, 2 * k + 1, 0, 2 * k + 3, 0⟩ [fm]⊢*
    ⟨k + 2, 0, 0, 0, 2 * k + 2⟩ := by
  intro k; induction' k with k ih
  · -- k = 0: (0, 1, 0, 3, 0) →* (2, 0, 0, 0, 2). Three steps: R5, R1, R2.
    step fm; step fm; step fm; finish
  · -- k+1: (0, 2k+3, 0, 2k+5, 0) →* (k+3, 0, 0, 0, 2k+4)
    -- Phase 1: R5, R1, R2 (3 steps)
    step fm; step fm; step fm
    -- Now at (2, 2k+2, 0, 2k+2, 2)
    -- Phase 2: r1r1r2_chain (k+1) rounds → (2, 0, k+1, 0, k+3)
    show ⟨2, 2 * k + 2, 0, 2 * k + 2, 2⟩ [fm]⊢* ⟨k + 1 + 2, 0, 0, 0, 2 * (k + 1) + 2⟩
    rw [show 2 * k + 2 = 0 + 2 * (k + 1) from by ring]
    apply stepStar_trans (r1r1r2_chain (k + 1) (B := 0) (C := 0) (D := 0) (E := 2))
    -- Now at (2, 0, k+1, 0, k+3)
    -- Phase 3: r3_r2_d0 (k+1) rounds → (k+3, 0, 0, 0, 2k+4)
    show ⟨2, 0, 0 + (k + 1), 0, 1 + 1 + (k + 1)⟩ [fm]⊢*
      ⟨k + 1 + (1 + 1), 0, 0, 0, (1 + 1) * (k + 1) + (1 + 1)⟩
    rw [show 0 + (k + 1) = k + 1 from by omega,
        show 1 + 1 + (k + 1) = k + 3 from by omega,
        show k + 1 + (1 + 1) = k + 3 from by omega,
        show (1 + 1) * (k + 1) + (1 + 1) = 2 * k + 4 from by omega,
        show (2 : ℕ) = 1 + 1 from rfl]
    apply stepStar_trans (r3_r2_d0 (k + 1) (a := 1) (e := k + 3))
    ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, 2n+2) ⊢⁺ (n+3, 0, 0, 0, 2n+4)
theorem main_trans : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
  -- Phase 1: R3 chain (n+2 steps): (n+2, 0, 0, 0, 2n+2) →* (0, 0, 0, 2n+4, 2n+2)
  step fm
  apply stepStar_trans (r3_chain (n + 1) (d := 2) (e := 2 * n + 2))
  -- Phase 2: R4 chain: (0, 0, 0, 2n+4, 2n+2) →* (0, 2n+2, 0, 2n+4, 0)
  rw [show 2 + 2 * (n + 1) = 2 * n + 4 from by ring]
  apply stepStar_trans (r4_chain (2 * n + 2) (b := 0) (d := 2 * n + 4))
  -- Phase 3: process_even (n+1): (0, 2n+2, 0, 2n+4, 0) →* (n+2, 0, 0, 1, 2n+3)
  rw [show 0 + (2 * n + 2) = 2 * (n + 1) from by ring,
      show 2 * n + 4 = 2 * (n + 1) + 2 from by ring]
  apply stepStar_trans (process_even (n + 1))
  -- Phase 4: R3 chain: (n+2, 0, 0, 1, 2n+3) →* (0, 0, 0, 2n+5, 2n+3)
  rw [show n + 1 + 1 = n + 2 from by ring,
      show 2 * (n + 1) + 1 = 2 * n + 3 from by ring]
  apply stepStar_trans (r3_chain (n + 2) (d := 1) (e := 2 * n + 3))
  -- Phase 5: R4 chain: (0, 0, 0, 2n+5, 2n+3) →* (0, 2n+3, 0, 2n+5, 0)
  rw [show 1 + 2 * (n + 2) = 2 * n + 5 from by ring]
  apply stepStar_trans (r4_chain (2 * n + 3) (b := 0) (d := 2 * n + 5))
  -- Phase 6: process_odd (n+1): (0, 2n+3, 0, 2n+5, 0) →* (n+3, 0, 0, 0, 2n+4)
  rw [show 0 + (2 * n + 3) = 2 * (n + 1) + 1 from by ring,
      show 2 * n + 5 = 2 * (n + 1) + 3 from by ring]
  apply stepStar_trans (process_odd (n + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩) 0
  intro n
  exact ⟨n + 1, main_trans⟩

end Sz22_2003_unofficial_1123
