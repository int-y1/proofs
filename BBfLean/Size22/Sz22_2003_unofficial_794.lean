import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #794: [35/6, 605/2, 4/77, 3/5, 2/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  1  0  2
 2  0  0 -1 -1
 0  1 -1  0  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_794

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: move c to b
theorem c_to_b : ∀ k b, ⟨(0 : ℕ), b, c + k, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- R1R1R3 loop: each round does R1,R1,R3
-- (2, b+2, c, d, e+1) -> R1 -> (1, b+1, c+1, d+1, e+1) -> R1 -> (0, b, c+2, d+2, e+1) -> R3 -> (2, b, c+2, d+1, e)
theorem r1r1r3_loop : ∀ k, ∀ c d e, ⟨(2 : ℕ), 2 * k, c, d, e + k⟩ [fm]⊢* ⟨(2 : ℕ), 0, c + 2 * k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    rw [show c + 1 + 1 = c + 2 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) (d + 1) e)
    ring_nf; finish

-- R3R2R2 loop: each round does R3,R2,R2
-- (0, 0, c, d+1, e+1) -> R3 -> (2, 0, c, d, e) -> R2 -> (1, 0, c+1, d, e+2) -> R2 -> (0, 0, c+2, d, e+4)
theorem r3r2r2_loop : ∀ k, ∀ c d e, ⟨(0 : ℕ), 0, c, d + k, e + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 2 * k, d, e + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm; step fm
    rw [show c + 1 + 1 = c + 2 from by ring,
        show e + k + 2 + 2 = (e + 4) + k from by ring]
    apply stepStar_trans (ih (c + 2) d (e + 4))
    ring_nf; finish

-- Phase 5 wrapper: stated in the exact form that arises after step fm
theorem phase5 (c : ℕ) : ⟨(2 : ℕ), 2 * c, 1, 0, 2 * c⟩ [fm]⊢* ⟨(2 : ℕ), 0, 2 * c + 1, c, c⟩ := by
  have h := r1r1r3_loop c 1 0 c
  -- h : (2, 2*c, 1, 0, c+c) ⊢* (2, 0, 1+2*c, 0+c, c)
  -- Need: (2, 2*c, 1, 0, 2*c) ⊢* (2, 0, 2*c+1, c, c)
  -- These differ only in concrete arithmetic: 2*c vs c+c, 1+2*c vs 2*c+1, 0+c vs c.
  -- All equalities are by omega.
  have e1 : c + c = 2 * c := by omega
  have e2 : 1 + 2 * c = 2 * c + 1 := by omega
  have e3 : 0 + c = c := by omega
  rw [e1, e2, e3] at h
  exact h

-- Phase 7 wrapper
theorem phase7 (c : ℕ) : ⟨(0 : ℕ), 0, 2 * c + 3, c, c + 4⟩ [fm]⊢* ⟨(0 : ℕ), 0, 4 * c + 3, 0, 4 * c + 4⟩ := by
  have h := r3r2r2_loop c (2 * c + 3) 0 4
  -- h : (0, 0, 2c+3, 0+c, 4+c) ⊢* (0, 0, 2c+3+2c, 0, 4+4c)
  have e1 : 0 + c = c := by omega
  have e2 : 4 + c = c + 4 := by omega
  have e3 : 2 * c + 3 + 2 * c = 4 * c + 3 := by omega
  have e4 : 4 + 4 * c = 4 * c + 4 := by omega
  rw [e1, e2, e3, e4] at h
  exact h

-- Full transition: (0, 0, 2c+1, 0, 2c+2) ⊢⁺ (0, 0, 4c+3, 0, 4c+4)
theorem main_trans (c : ℕ) : ⟨(0 : ℕ), 0, 2 * c + 1, 0, 2 * c + 2⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 4 * c + 3, 0, 4 * c + 4⟩ := by
  -- Phase 1: R4 chain
  rw [show (2 * c + 1 : ℕ) = 0 + (2 * c + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (c_to_b (2 * c + 1) 0 (c := 0) (e := 2 * c + 2))
  rw [show 0 + (2 * c + 1) = (2 * c) + 1 from by ring,
      show (2 * c + 2 : ℕ) = (2 * c + 1) + 1 from by ring]
  -- Phase 2: R5
  step fm
  -- Phase 3: R1
  step fm
  -- Phase 4: R3
  rw [show (2 * c + 1 : ℕ) = (2 * c) + 1 from by ring]
  step fm
  -- Phase 5: R1R1R3 loop
  apply stepStar_trans (phase5 c)
  -- Phase 6: R2R2
  step fm
  rw [show 2 * c + 1 + 1 = 2 * c + 2 from by ring]
  step fm
  rw [show 2 * c + 2 + 1 = 2 * c + 3 from by ring,
      show c + 2 + 2 = c + 4 from by ring]
  -- Phase 7: R3R2R2 loop
  exact phase7 c

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun c ↦ ⟨0, 0, 2 * c + 1, 0, 2 * c + 2⟩) 0
  intro c; refine ⟨2 * c + 1, ?_⟩
  rw [show 2 * (2 * c + 1) + 1 = 4 * c + 3 from by ring,
      show 2 * (2 * c + 1) + 2 = 4 * c + 4 from by ring]
  exact main_trans c
