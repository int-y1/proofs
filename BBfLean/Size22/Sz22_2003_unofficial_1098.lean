import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1098: [5/6, 3773/2, 2/35, 3/49, 10/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  3  1
 1  0 -1 -1  0
 0  1  0 -2  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1098

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 chain: (0, b, 0, d+2*k, e) →* (0, b+k, 0, d, e)
theorem r4_chain : ∀ k, ∀ b d, ⟨0, b, 0, d + 2 * k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- Drain loop: (1, k, c, 0, k) →* (1, 0, c+2*k, 0, 0)
theorem drain_loop : ∀ k, ⟨1, k, c, 0, k⟩ [fm]⊢* ⟨1, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · step fm -- R1: (0, k, c+1, 0, k+1)
    step fm -- R5: (1, k, c+2, 0, k)
    apply stepStar_trans (ih (c := c + 2))
    ring_nf; finish

-- R3+R2 chain: (0, 0, k, d+1, e) →* (0, 0, 0, d+1+2*k, e+k)
theorem r3r2_chain : ∀ k, ∀ d e, ⟨0, 0, k, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 1 + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm -- R3: (1, 0, k, d, e)
    step fm -- R2: (0, 0, k, d+3, e+1)
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, 2e+3, e+1) →⁺ (0, 0, 0, 4e+5, 2e+2)
theorem main_transition : ⟨0, 0, 0, 2 * e + 3, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * e + 5, 2 * e + 2⟩ := by
  -- First step: R4 (d = 2e+3 ≥ 2)
  rw [show 2 * e + 3 = (2 * e + 1) + 2 from by ring]
  step fm -- R4: (0, 1, 0, 2*e+1, e+1)
  -- Remaining R4s
  rw [show 2 * e + 1 = 1 + 2 * e from by ring]
  apply stepStar_trans (r4_chain e 1 1 (e := e + 1))
  -- Now at (0, e+1, 0, 1, e+1)
  rw [show 1 + e = e + 1 from by ring]
  step fm -- R5: (1, e+1, 1, 1, e)
  step fm -- R1: (0, e, 2, 1, e)
  step fm -- R3: (1, e, 1, 0, e)
  -- Drain loop
  apply stepStar_trans (drain_loop e (c := 1))
  -- Now at (1, 0, 1+2*e, 0, 0)
  step fm -- R2: (0, 0, 1+2*e, 3, 1)
  -- R3+R2 chain
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (1 + 2 * e) 2 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨0, 0, 0, 2 * e + 3, e + 1⟩) 0
  intro e
  refine ⟨2 * e + 1, ?_⟩
  show ⟨0, 0, 0, 2 * e + 3, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (2 * e + 1) + 3, (2 * e + 1) + 1⟩
  rw [show 2 * (2 * e + 1) + 3 = 4 * e + 5 from by ring,
      show (2 * e + 1) + 1 = 2 * e + 2 from by ring]
  exact main_transition
