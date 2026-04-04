import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1767: [9/10, 22/21, 49/2, 5/121, 9/7]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  1
-1  0  0  2  0
 0  0  1  0 -2
 0  2  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1767

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R3 chain: (a, 0, 0, D, e) →* (0, 0, 0, D+2*a, e)
theorem r3_chain : ∀ a, ⟨a, 0, 0, D, e⟩ [fm]⊢* ⟨0, 0, 0, D + 2 * a, e⟩ := by
  intro a; induction' a with a ih generalizing D
  · exists 0
  · step fm
    apply stepStar_trans (ih (D := D + 2))
    ring_nf; finish

-- R4 chain: (0, 0, c, d, 2*k) →* (0, 0, c+k, d, 0)
theorem r4_chain : ∀ k, ⟨0, 0, c, d, 2 * k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R2/R1 interleave: (0, b+2, k, k+1, e) →* (0, b+k+2, 0, 1, e+k)
theorem r2r1_chain : ∀ k, ∀ b e, ⟨0, b + 2, k, k + 1, e⟩ [fm]⊢* ⟨0, b + k + 2, 0, 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    step fm
    rw [show b + 2 + 1 = (b + 1) + 2 from by ring,
        show k + 1 = (k + 1) from rfl]
    apply stepStar_trans (ih (b := b + 1) (e := e + 1))
    ring_nf; finish

-- Drain step (b≥2): (a+1, b+2, 0, 0, e) →* (a+2, b, 0, 0, e+2)
theorem drain_step : ⟨a + 1, b + 2, 0, 0, e⟩ [fm]⊢* ⟨a + 2, b, 0, 0, e + 2⟩ := by
  step fm
  step fm
  step fm
  finish

-- Drain (b=0): (a, 0, 0, 0, e) →* (0, 0, 0, 2*a, e)
-- This is just r3_chain with D=0
theorem drain_b0 : ⟨a, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a, e⟩ := by
  rw [show (0 : ℕ) = 0 + 0 from rfl]
  rw [show 2 * a = 0 + 2 * a from by ring]
  exact r3_chain a

-- Drain (b=1): (a+1, 1, 0, 0, e) →* (0, 0, 0, 2*a+3, e+1)
theorem drain_b1 : ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 3, e + 1⟩ := by
  step fm
  step fm
  show ⟨a + 1, 0, 0, 1, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 3, e + 1⟩
  rw [show (1 : ℕ) = 0 + 2 * 0 + 1 from by ring,
      show 2 * a + 3 = 0 + 2 * 0 + 1 + 2 * (a + 1) from by ring]
  exact r3_chain (a + 1)

-- Full drain: (a+1, b, 0, 0, e) →* (0, 0, 0, 2*a+b+2, e+b)
theorem drain : ∀ b, ∀ a e, ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + b + 2, e + b⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a e
  rcases b with _ | _ | b
  · -- b = 0
    rw [show 2 * a + 0 + 2 = 2 * (a + 1) from by ring]
    exact drain_b0
  · -- b = 1
    exact drain_b1
  · -- b + 2
    apply stepStar_trans drain_step
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih b (by omega) (a + 1) (e + 2))
    ring_nf; finish

-- Main transition for n ≥ 1: (0, 0, n+1, n+3, 0) ⊢⁺ (0, 0, n+2, n+4, 0)
theorem main_trans : ⟨0, 0, n + 1, n + 3, 0⟩ [fm]⊢⁺ ⟨0, 0, n + 2, n + 4, 0⟩ := by
  -- R5: (0, 0, n+1, n+3, 0) → (0, 2, n+1, n+2, 0)
  step fm
  -- R2/R1 interleave: (0, 2, n+1, n+2, 0) →* (0, n+3, 0, 1, n+1)
  rw [show (2 : ℕ) = 0 + 2 from by ring,
      show n + 2 = (n + 1) + 1 from by ring]
  apply stepStar_trans (r2r1_chain (n + 1) 0 0)
  rw [show 0 + (n + 1) + 2 = n + 3 from by ring,
      show 0 + (n + 1) = n + 1 from by ring]
  -- R2: (0, n+3, 0, 1, n+1) → (1, n+2, 0, 0, n+2)
  step fm
  -- Drain: (1, n+2, 0, 0, n+2) →* (0, 0, 0, n+4, 2n+4)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain (n + 2) 0 (n + 2))
  rw [show 2 * 0 + (n + 2) + 2 = n + 4 from by ring,
      show n + 2 + (n + 2) = 2 * (n + 2) from by ring]
  -- R4 chain: (0, 0, 0, n+4, 2*(n+2)) →* (0, 0, n+2, n+4, 0)
  apply stepStar_trans (r4_chain (n + 2) (c := 0) (d := n + 4))
  ring_nf; finish

-- Base case: (0, 0, 0, 2, 0) ⊢⁺ (0, 0, 1, 3, 0)
theorem base_trans : ⟨0, 0, 0, 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 1, 3, 0⟩ := by
  execute fm 6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n, n + 2, 0⟩) 0
  intro n
  rcases n with _ | n
  · exact ⟨1, base_trans⟩
  · exact ⟨n + 2, main_trans⟩
