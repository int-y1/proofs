import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #376: [2/15, 9/154, 175/2, 121/5, 2/11]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1 -1
-1  0  2  1  0
 0  0 -1  0  2
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_376

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R3 chain: (a+j, 0, c, d, 0) ⊢* (a, 0, c+2*j, d+j, 0)
theorem r3_chain : ∀ j a c d,
    ⟨a+j, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*j, d+j, 0⟩ := by
  intro j; induction' j with j ih <;> intro a c d
  · exists 0
  rw [show a + (j + 1) = (a + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: (0, 0, c+j, d, e) ⊢* (0, 0, c, d, e+2*j)
theorem r4_chain : ∀ j c d e,
    ⟨0, 0, c+j, d, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*j⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · exists 0
  rw [show c + (j + 1) = (c + j) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5+R2 step: (0, b, 0, d+1, e+2) ⊢* (0, b+2, 0, d, e)
theorem r5r2_step : ∀ b d e,
    ⟨0, b, 0, d+1, e+2⟩ [fm]⊢* ⟨0, b+2, 0, d, e⟩ := by
  intro b d e; step fm; step fm; finish

-- R5+R2 chain: (0, b, 0, d+j, e+2*j) ⊢* (0, b+2*j, 0, d, e)
theorem r5r2_chain : ∀ j b d e,
    ⟨0, b, 0, d+j, e+2*j⟩ [fm]⊢* ⟨0, b+2*j, 0, d, e⟩ := by
  intro j; induction' j with j ih <;> intro b d e
  · exists 0
  rw [show d + (j + 1) = (d + j) + 1 from by ring,
      show e + 2 * (j + 1) = (e + 2 * j) + 2 from by ring]
  apply stepStar_trans (r5r2_step _ _ _)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 1 triple: (k+1, b+2, 0, k, 0) ⊢* (k+2, b, 0, k+1, 0)
theorem phase1_triple : ∀ k b,
    ⟨k+1, b+2, 0, k, 0⟩ [fm]⊢* ⟨k+2, b, 0, k+1, 0⟩ := by
  intro k b; step fm; step fm; step fm; ring_nf; finish

-- Phase 1 loop: (k+1, b+2*j, 0, k, 0) ⊢* (k+1+j, b, 0, k+j, 0)
theorem phase1_loop : ∀ j k b,
    ⟨k+1, b+2*j, 0, k, 0⟩ [fm]⊢* ⟨k+1+j, b, 0, k+j, 0⟩ := by
  intro j; induction' j with j ih <;> intro k b
  · exists 0
  rw [show b + 2 * (j + 1) = (b + 2 * j) + 2 from by ring]
  apply stepStar_trans (phase1_triple _ _)
  rw [show k + 1 + 1 = (k + 1) + 1 from by ring,
      show k + 1 = k + 1 from rfl]
  apply stepStar_trans (ih (k + 1) _)
  ring_nf; finish

-- Opening: (1, b+2, 0, 0, 0) ⊢* (2, b, 0, 1, 0)
theorem opening : ∀ b,
    ⟨1, b+2, 0, 0, 0⟩ [fm]⊢* ⟨2, b, 0, 1, 0⟩ := by
  intro b; step fm; step fm; step fm; ring_nf; finish

-- Tail: (0, b+6, 0, 0, 2) ⊢⁺ (1, b+6, 0, 0, 0)
-- R5: (1, b+6, 0, 0, 1)
-- R3: (0, b+6, 2, 1, 1)
-- R1: (1, b+5, 1, 1, 1)
-- R1: (2, b+4, 0, 1, 1)
-- R2: (1, b+6, 0, 0, 0)
theorem tail : ∀ b,
    ⟨0, b+6, 0, 0, 2⟩ [fm]⊢⁺ ⟨1, b+6, 0, 0, 0⟩ := by
  intro b; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- Main cycle: (1, 2*n+2, 0, 0, 0) ⊢⁺ (1, 4*n+6, 0, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨1, 2*n+2, 0, 0, 0⟩ [fm]⊢⁺ ⟨1, 4*n+6, 0, 0, 0⟩ := by
  -- Opening: (1, 2n+2, 0, 0, 0) ⊢* (2, 2n, 0, 1, 0)
  apply stepStar_stepPlus_stepPlus
  · rw [show 2 * n + 2 = 2 * n + 2 from rfl]
    exact opening (2 * n)
  -- Phase 1 loop n times: (2, 2n, 0, 1, 0) ⊢* (n+2, 0, 0, n+1, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := phase1_loop n 1 0
    rw [show 0 + 2 * n = 2 * n from by ring,
        show 1 + 1 + n = n + 2 from by ring,
        show 1 + n = n + 1 from by ring] at h
    exact h
  -- R3 chain: (n+2, 0, 0, n+1, 0) ⊢* (0, 0, 2n+4, 2n+3, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := r3_chain (n + 2) 0 0 (n + 1)
    rw [show 0 + (n + 2) = n + 2 from by ring,
        show 0 + 2 * (n + 2) = 2 * n + 4 from by ring,
        show n + 1 + (n + 2) = 2 * n + 3 from by ring] at h
    exact h
  -- R4 chain: (0, 0, 2n+4, 2n+3, 0) ⊢* (0, 0, 0, 2n+3, 4n+8)
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (2 * n + 4) 0 (2 * n + 3) 0
    rw [show 0 + (2 * n + 4) = 2 * n + 4 from by ring,
        show 0 + 2 * (2 * n + 4) = 4 * n + 8 from by ring] at h
    exact h
  -- R5R2 chain: (0, 0, 0, 2n+3, 4n+8) ⊢* (0, 4n+6, 0, 0, 2)
  apply stepStar_stepPlus_stepPlus
  · have h := r5r2_chain (2 * n + 3) 0 0 2
    rw [show 0 + (2 * n + 3) = 2 * n + 3 from by ring,
        show 2 + 2 * (2 * n + 3) = 4 * n + 8 from by ring,
        show 0 + 2 * (2 * n + 3) = 4 * n + 6 from by ring] at h
    exact h
  -- Tail: (0, 4n+6, 0, 0, 2) ⊢⁺ (1, 4n+6, 0, 0, 0)
  rw [show 4 * n + 6 = 4 * n + 0 + 6 from by ring]
  exact tail (4 * n + 0)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 2, 0, 0, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 2*n+2, 0, 0, 0⟩) 0
  intro n
  refine ⟨2*n+2, ?_⟩
  rw [show 2 * (2 * n + 2) + 2 = 4 * n + 6 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_376
