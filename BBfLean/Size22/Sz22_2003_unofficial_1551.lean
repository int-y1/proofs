import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1551: [7/30, 605/3, 3/77, 2/11, 63/2]

Vector representation:
```
-1 -1 -1  1  0
 0 -1  1  0  2
 0  1  0 -1 -1
 1  0  0  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1551

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- Inner step: R5, R1, R1. (a+3, 0, c+2, d, 0) ->* (a, 0, c, d+3, 0)
theorem inner_step_chain : ∀ k a c d, ⟨a + 3 * k, 0, c + 2 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih
  · intro a c d; exists 0
  · intro a c d
    rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3)); ring_nf; finish

-- R3/R2 chain: (0, 0, c, d+k, e) ->* (0, 0, c+k, d, e+k) when e >= 1
theorem r3r2_chain : ∀ k c d e, ⟨0, 0, c, d + k, e + 1⟩ [fm]⊢* ⟨0, 0, c + k, d, e + k + 1⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) d (e + 1)); ring_nf; finish

-- R4 chain: (a, 0, c, 0, e+k) ->* (a+k, 0, c, 0, e)
theorem r4_chain : ∀ k a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) c e); ring_nf; finish

-- T1: (6j+5, 0, 2j²+6j+3, 0, 0) ⊢⁺ (6j+7, 0, 2j²+8j+6, 0, 0)
theorem main_t1 (j : ℕ) :
    ⟨6 * j + 5, 0, 2 * j ^ 2 + 6 * j + 3, 0, 0⟩ [fm]⊢⁺
    ⟨6 * j + 7, 0, 2 * j ^ 2 + 8 * j + 6, 0, 0⟩ := by
  -- Phase 1: inner chain with k = 2j+1 steps
  rw [show 6 * j + 5 = 2 + 3 * (2 * j + 1) from by ring,
      show 2 * j ^ 2 + 6 * j + 3 = (2 * j ^ 2 + 2 * j + 1) + 2 * (2 * j + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (inner_step_chain (2 * j + 1) 2 (2 * j ^ 2 + 2 * j + 1) 0)
  rw [show 0 + 3 * (2 * j + 1) = 6 * j + 3 from by ring]
  -- Phase 2: drain from a=2: R5, R1, R2
  step fm; step fm; step fm
  rw [show 2 * j ^ 2 + 2 * j + 1 = (2 * j ^ 2 + 2 * j + 1) from by ring]
  -- Phase 3: R3/R2 chain for 6j+5 rounds
  rw [show 6 * j + 5 = (0 : ℕ) + (6 * j + 5) from by ring,
      show (2 : ℕ) = 0 + 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (6 * j + 5) (2 * j ^ 2 + 2 * j + 1) 0 1)
  rw [show 2 * j ^ 2 + 2 * j + 1 + (6 * j + 5) = 2 * j ^ 2 + 8 * j + 6 from by ring,
      show 1 + (6 * j + 5) + 1 = 0 + (6 * j + 7) from by ring]
  -- Phase 4: R4 chain for 6j+7 rounds
  apply stepStar_trans (r4_chain (6 * j + 7) 0 (2 * j ^ 2 + 8 * j + 6) 0)
  ring_nf; finish

-- T2: (6j+7, 0, 2j²+8j+6, 0, 0) ⊢⁺ (6j+11, 0, 2j²+10j+11, 0, 0)
theorem main_t2 (j : ℕ) :
    ⟨6 * j + 7, 0, 2 * j ^ 2 + 8 * j + 6, 0, 0⟩ [fm]⊢⁺
    ⟨6 * j + 11, 0, 2 * j ^ 2 + 10 * j + 11, 0, 0⟩ := by
  -- Phase 1: inner chain with k = 2j+2 steps
  rw [show 6 * j + 7 = 1 + 3 * (2 * j + 2) from by ring,
      show 2 * j ^ 2 + 8 * j + 6 = (2 * j ^ 2 + 4 * j + 2) + 2 * (2 * j + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (inner_step_chain (2 * j + 2) 1 (2 * j ^ 2 + 4 * j + 2) 0)
  rw [show 0 + 3 * (2 * j + 2) = 6 * j + 6 from by ring]
  -- Phase 2: drain from a=1: R5, R2, R2
  step fm; step fm; step fm
  rw [show 2 * j ^ 2 + 4 * j + 2 + 2 = 2 * j ^ 2 + 4 * j + 4 from by ring,
      show 6 * j + 6 + 1 = (0 : ℕ) + (6 * j + 7) from by ring,
      show (4 : ℕ) = 0 + 3 + 1 from by ring]
  -- Phase 3: R3/R2 chain for 6j+7 rounds
  apply stepStar_trans (r3r2_chain (6 * j + 7) (2 * j ^ 2 + 4 * j + 4) 0 3)
  rw [show 2 * j ^ 2 + 4 * j + 4 + (6 * j + 7) = 2 * j ^ 2 + 10 * j + 11 from by ring,
      show 3 + (6 * j + 7) + 1 = 0 + (6 * j + 11) from by ring]
  -- Phase 4: R4 chain for 6j+11 rounds
  apply stepStar_trans (r4_chain (6 * j + 11) 0 (2 * j ^ 2 + 10 * j + 11) 0)
  ring_nf; finish

-- Combined macro transition: j -> j+1
theorem main_trans (j : ℕ) :
    ⟨6 * j + 5, 0, 2 * j ^ 2 + 6 * j + 3, 0, 0⟩ [fm]⊢⁺
    ⟨6 * (j + 1) + 5, 0, 2 * (j + 1) ^ 2 + 6 * (j + 1) + 3, 0, 0⟩ := by
  rw [show 6 * (j + 1) + 5 = 6 * j + 11 from by ring,
      show 2 * (j + 1) ^ 2 + 6 * (j + 1) + 3 = 2 * j ^ 2 + 10 * j + 11 from by ring]
  exact stepPlus_trans (main_t1 j) (main_t2 j)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 3, 0, 0⟩)
  · execute fm 10
  have key := progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun j ↦ ⟨6 * j + 5, 0, 2 * j ^ 2 + 6 * j + 3, 0, 0⟩) 0
    (fun j ↦ ⟨j + 1, main_trans j⟩)
  simpa using key

end Sz22_2003_unofficial_1551
