import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1461: [7/15, 3/77, 250/7, 11/25, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1  0  3 -1  0
 0  0 -2  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1461

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+3, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3 chain: consume d, add to a and c
theorem r3_chain : ∀ k a c, ⟨a, (0 : ℕ), c, k, (0 : ℕ)⟩ [fm]⊢* ⟨a + k, (0 : ℕ), c + 3 * k, 0, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show (k + 1) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) (c + 3))
    ring_nf; finish

-- R4 chain: consume pairs of c, add to e
theorem r4_chain : ∀ k a e, ⟨a, (0 : ℕ), 2 * k, 0, e⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- R4 chain with leftover 1: consume pairs of c leaving 1, add to e
theorem r4_chain_odd : ∀ k a e, ⟨a, (0 : ℕ), 2 * k + 1, 0, e⟩ [fm]⊢* ⟨a, (0 : ℕ), 1, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- R1 chain: consume b and c together
theorem r1_chain : ∀ k a b c d e, ⟨a, b + k, c + k, d, e⟩ [fm]⊢* ⟨a, b, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c d e
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    apply stepStar_trans (ih a (b + 1) (c + 1) d e)
    step fm
    rw [show d + k + 1 = d + (k + 1) from by ring]
    finish

-- R2,R5 chain: (k, B, 0, 1, k) →* (0, B+2k, 0, 1, 0)
theorem r2r5_chain : ∀ k B, ⟨k, B, (0 : ℕ), 1, k⟩ [fm]⊢* ⟨(0 : ℕ), B + 2 * k, 0, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro B
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (B + 2))
    ring_nf; finish

-- Drain from d=2: (A+1, 0, 0, 2, A+2) →* (0, 2A+3, 0, 1, 0)
theorem drain_d2 (A : ℕ) : ⟨A + 1, (0 : ℕ), (0 : ℕ), 2, A + 2⟩ [fm]⊢* ⟨(0 : ℕ), 2 * A + 3, 0, 1, 0⟩ := by
  step fm
  step fm
  step fm
  apply stepStar_trans (r2r5_chain A 3)
  ring_nf; finish

-- R3/R1x3 interleaved chain: k rounds of (R3, R1, R1, R1)
theorem r3r1x3_chain : ∀ k j B d, ⟨j, B + 3 * k, (0 : ℕ), d + 1, (0 : ℕ)⟩ [fm]⊢* ⟨j + k, B, 0, d + 2 * k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro j B d
  · exists 0
  · rw [show B + 3 * (k + 1) = (B + 3) + 3 * k from by ring]
    apply stepStar_trans (ih j (B + 3) d)
    rw [show d + 2 * k + 1 = (d + 2 * k) + 1 from by ring]
    step fm -- R3: (j+k+1, B+3, 3, d+2k, 0)
    rw [show B + 3 = B + 0 + 3 from by ring,
        show (3 : ℕ) = 0 + 3 from by ring]
    apply stepStar_trans (r1_chain 3 (j + k + 1) (B + 0) 0 (d + 2 * k) 0)
    ring_nf; finish

-- Main transition: (a+1, 0, 0, 2a+3, 0) →⁺ (4a+5, 0, 0, 8a+11, 0)
theorem main_trans (a : ℕ) :
    ⟨a + 1, (0 : ℕ), 0, 2 * a + 3, 0⟩ [fm]⊢⁺ ⟨4 * a + 5, (0 : ℕ), 0, 8 * a + 11, 0⟩ := by
  -- Phase A: first R3 step to establish ⊢⁺, then R3 x (2a+2)
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨a + 1, (0 : ℕ), 0, (2 * a + 3), 0⟩ : Q) [fm]⊢ ⟨a + 2, 0, 3, 2 * a + 2, 0⟩)
  apply stepStar_trans (r3_chain (2 * a + 2) (a + 2) 3)
  rw [show a + 2 + (2 * a + 2) = 3 * a + 4 from by ring,
      show 3 + 3 * (2 * a + 2) = 6 * a + 9 from by ring]
  -- State: (3a+4, 0, 6a+9, 0, 0)
  -- Phase B: R4 x (3a+4), 6a+9 = 2(3a+4)+1 is odd
  rw [show 6 * a + 9 = 2 * (3 * a + 4) + 1 from by ring]
  apply stepStar_trans (r4_chain_odd (3 * a + 4) (3 * a + 4) 0)
  rw [show (0 : ℕ) + (3 * a + 4) = 3 * a + 4 from by ring]
  -- State: (3a+4, 0, 1, 0, 3a+4)
  -- Phase C: R5, R1
  rw [show 3 * a + 4 = (3 * a + 3) + 1 from by ring]
  step fm -- R5
  step fm -- R1
  -- State: (3a+3, 0, 0, 2, 3a+4)
  -- Phase D: Drain
  rw [show 3 * a + 3 = (3 * a + 2) + 1 from by ring,
      show 3 * a + 4 = (3 * a + 2) + 2 from by ring]
  apply stepStar_trans (drain_d2 (3 * a + 2))
  rw [show 2 * (3 * a + 2) + 3 = 6 * a + 7 from by ring]
  -- State: (0, 6a+7, 0, 1, 0)
  -- Phase E: R3/R1x3 chain x (2a+2) rounds
  rw [show 6 * a + 7 = 1 + 3 * (2 * a + 2) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1x3_chain (2 * a + 2) 0 1 0)
  rw [show (0 : ℕ) + (2 * a + 2) = 2 * a + 2 from by ring,
      show 0 + 2 * (2 * a + 2) + 1 = 4 * a + 5 from by ring]
  -- State: (2a+2, 1, 0, 4a+5, 0)
  -- Phase F: Partial round: R3, then 1 R1
  rw [show 4 * a + 5 = (4 * a + 4) + 1 from by ring]
  step fm -- R3
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show (3 : ℕ) = 2 + 1 from by ring]
  step fm -- R1
  rw [show 4 * a + 4 + 1 = 4 * a + 5 from by ring]
  -- State: (2a+3, 0, 2, 4a+5, 0)
  -- Phase G: R3 x (4a+5)
  apply stepStar_trans (r3_chain (4 * a + 5) (2 * a + 3) 2)
  rw [show 2 * a + 3 + (4 * a + 5) = 6 * a + 8 from by ring,
      show 2 + 3 * (4 * a + 5) = 12 * a + 17 from by ring]
  -- State: (6a+8, 0, 12a+17, 0, 0)
  -- Phase H: R4 x (6a+8), 12a+17 = 2(6a+8)+1 is odd
  rw [show 12 * a + 17 = 2 * (6 * a + 8) + 1 from by ring]
  apply stepStar_trans (r4_chain_odd (6 * a + 8) (6 * a + 8) 0)
  rw [show (0 : ℕ) + (6 * a + 8) = 6 * a + 8 from by ring]
  -- State: (6a+8, 0, 1, 0, 6a+8)
  -- Phase I: R5, R1
  rw [show 6 * a + 8 = (6 * a + 7) + 1 from by ring]
  step fm -- R5
  step fm -- R1
  -- State: (6a+7, 0, 0, 2, 6a+8)
  -- Phase J: Drain
  rw [show 6 * a + 7 = (6 * a + 6) + 1 from by ring,
      show 6 * a + 8 = (6 * a + 6) + 2 from by ring]
  apply stepStar_trans (drain_d2 (6 * a + 6))
  rw [show 2 * (6 * a + 6) + 3 = 12 * a + 15 from by ring]
  -- State: (0, 12a+15, 0, 1, 0)
  -- Phase K: R3/R1x3 chain x (4a+5) rounds
  rw [show 12 * a + 15 = 0 + 3 * (4 * a + 5) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1x3_chain (4 * a + 5) 0 0 0)
  rw [show (0 : ℕ) + (4 * a + 5) = 4 * a + 5 from by ring,
      show 0 + 2 * (4 * a + 5) + 1 = 8 * a + 11 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 3, 0⟩) (by execute fm 15)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 2 * n + 3, 0⟩) 0
  intro n
  refine ⟨4 * n + 4, ?_⟩
  show ⟨n + 1, (0 : ℕ), 0, 2 * n + 3, 0⟩ [fm]⊢⁺ ⟨4 * n + 4 + 1, (0 : ℕ), 0, 2 * (4 * n + 4) + 3, 0⟩
  rw [show 4 * n + 4 + 1 = 4 * n + 5 from by ring,
      show 2 * (4 * n + 4) + 3 = 8 * n + 11 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1461
