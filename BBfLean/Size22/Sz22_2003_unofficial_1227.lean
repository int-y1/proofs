import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1227: [5/6, 572/35, 77/2, 3/13, 15/11]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  1
-1  0  0  1  1  0
 0  1  0  0  0 -1
 0  1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1227

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: move f to b
theorem f_to_b : ∀ k, ∀ b d e f, ⟨(0 : ℕ), b, 0, d, e, f + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [Nat.add_succ f k]; step fm
    apply stepStar_trans (ih (b + 1) d e f); ring_nf; finish

-- R3 repeated: drain a to d and e
theorem r3_drain_a : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [Nat.add_succ a k]; step fm
    apply stepStar_trans (ih a (d + 1) (e + 1) f); ring_nf; finish

-- R2R1R1 interleaved loop: k rounds
-- Net per round: b -= 2, c += 1, d -= 1, e += 1, f += 1
theorem r2r1r1_loop : ∀ k, ∀ b c d e f,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), b, c + k + 1, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e f)
    rw [show c + k + 1 = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + k + 2 = c + (k + 1) + 1 from by ring,
        show e + k + 1 = e + (k + 1) from by ring,
        show f + k + 1 = f + (k + 1) from by ring]
    finish

-- R2R3 alternation: k pairs of (R2, R3) then final R2
-- Each R2+R3 pair: a += 1, c -= 1, e += 2, f += 1
-- Final R2: a += 2, c -= 1, e += 1, f += 1, d: 1 -> 0
-- Total: a += k+2, c -= k+1, e += 2k+1, f += k+1, d: 1 -> 0
theorem r2r3_chain : ∀ k, ∀ a c e f,
    ⟨a, 0, c + k + 1, 1, e, f⟩ [fm]⊢* ⟨a + k + 2, 0, c, 0, e + 2 * k + 1, f + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · step fm; ring_nf; finish
  · rw [show c + (k + 1) + 1 = c + k + 1 + 1 from by ring,
        show a + (k + 1) + 2 = (a + 1) + k + 2 from by ring,
        show e + 2 * (k + 1) + 1 = (e + 2) + 2 * k + 1 from by ring,
        show f + (k + 1) + 1 = (f + 1) + k + 1 from by ring]
    step fm; step fm
    exact ih (a + 1) c (e + 2) (f + 1)

-- Main transition: canonical n -> canonical n+1
-- Canonical state: (0, 0, 0, n+2, 2n²+6n+5, 2n+2)
theorem main_transition (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, n + 2, 2 * n * n + 6 * n + 5, 2 * n + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, n + 3, 2 * n * n + 10 * n + 13, 2 * n + 4⟩ := by
  -- Phase 1: R4 x (2n+2): move f to b
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (f_to_b (2 * n + 2) 0 (n + 2) (2 * n * n + 6 * n + 5) 0)
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by ring]
  -- State: (0, 2n+2, 0, n+2, 2n²+6n+5, 0)
  -- Phase 2: R5 step
  rw [show 2 * n * n + 6 * n + 5 = (2 * n * n + 6 * n + 4) + 1 from by ring]
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨0, 2 * n + 2, 0, n + 2, (2 * n * n + 6 * n + 4) + 1, 0⟩ : Q) [fm]⊢
      ⟨0, 2 * n + 3, 1, n + 2, 2 * n * n + 6 * n + 4, 0⟩)
  -- State: (0, 2n+3, 1, n+2, 2n²+6n+4, 0)
  -- Phase 3: n rounds of R2R1R1
  rw [show 2 * n + 3 = 3 + 2 * n from by ring,
      show n + 2 = 2 + n from by ring]
  apply stepStar_trans (r2r1r1_loop n 3 0 2 (2 * n * n + 6 * n + 4) 0)
  rw [show (0 : ℕ) + n + 1 = n + 1 from by ring,
      show 2 * n * n + 6 * n + 4 + n = 2 * n * n + 7 * n + 4 from by ring,
      show (0 : ℕ) + n = n from by ring]
  -- State: (0, 3, n+1, 2, 2n²+7n+4, n)
  -- Phase 4: one more R2R1R1 round
  rw [show n + 1 = n + 1 from rfl,
      show 3 = 1 + 1 + 1 from by ring,
      show 2 = 1 + 1 from by ring]
  step fm; step fm; step fm
  -- State: (0, 1, n+2, 1, 2n²+7n+5, n+1)
  -- Phase 5: R2, R1
  rw [show n + 1 + 1 = (n + 1) + 1 from rfl]
  step fm; step fm
  -- State: (1, 0, n+2, 0, 2n²+7n+6, n+2)
  -- Phase 6: R3
  step fm
  -- State: (0, 0, n+2, 1, 2n²+7n+7, n+2)
  -- Phase 7: R2R3 chain with k = n+1
  rw [show 2 * n * n + 7 * n + 4 + 1 + 1 + 1 = 2 * n * n + 7 * n + 7 from by ring]
  rw [show n + 1 + 1 = 0 + (n + 1) + 1 from by omega]
  apply stepStar_trans (r2r3_chain (n + 1) 0 0 (2 * n * n + 7 * n + 7) (0 + (n + 1) + 1))
  rw [show (0 : ℕ) + (n + 1) + 2 = n + 3 from by ring,
      show 2 * n * n + 7 * n + 7 + 2 * (n + 1) + 1 = 2 * n * n + 9 * n + 10 from by ring,
      show (0 : ℕ) + (n + 1) + 1 + (n + 1) + 1 = 2 * n + 4 from by ring]
  -- State: (n+3, 0, 0, 0, 2n²+9n+10, 2n+4)
  -- Phase 8: R3 drain a
  rw [show n + 3 = 0 + (n + 3) from by ring]
  apply stepStar_trans (r3_drain_a (n + 3) 0 0 (2 * n * n + 9 * n + 10) (2 * n + 4))
  rw [show (0 : ℕ) + (n + 3) = n + 3 from by ring,
      show 2 * n * n + 9 * n + 10 + (n + 3) = 2 * n * n + 10 * n + 13 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 2 * n * n + 6 * n + 5, 2 * n + 2⟩) 0
  intro n; exists n + 1
  have h := main_transition n
  rw [show 2 * (n + 1) * (n + 1) + 6 * (n + 1) + 5 = 2 * n * n + 10 * n + 13 from by ring,
      show 2 * (n + 1) + 2 = 2 * n + 4 from by ring]
  exact h

end Sz22_2003_unofficial_1227
