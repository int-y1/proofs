import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1158: [5/6, 44/35, 77/2, 3/121, 10/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  1  1
 0  1  0  0 -2
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1158

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R3 repeated: drain a to d and e.
theorem r3_drain : ∀ k, ∀ d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1) (e + 1)); ring_nf; finish

-- R4 repeated: drain e by pairs to b.
theorem r4_drain : ∀ k, ∀ b e, ⟨0, b, 0, d, e + 2 * k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · simp; exists 0
  · rw [show e + 2 * (k + 1) = e + 2 * k + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e); ring_nf; finish

-- R1,R1,R2 chain.
theorem r1r1r2_chain : ∀ k, ∀ c e, ⟨2, 2 * k + 1, c, k, e⟩ [fm]⊢* ⟨2, 1, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · simp; exists 0
  · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 from by ring]
    step fm
    rw [show 2 * k + 1 + 1 = 2 * k + 1 + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (e + 1)); ring_nf; finish

-- R3+R2 chain: (a+1, 0, c+k, 0, e) →* (a+k+1, 0, c, 0, e+2*k)
-- a must be quantified since it changes each round.
theorem r3r2_chain : ∀ k, ∀ a c e, ⟨a + 1, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · simp; exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring]
    step fm; step fm
    -- State: (a + 2, 0, c + k, 0, e + 1 + 1)
    -- a + 2 = (a + 1) + 1 by def, e + 1 + 1 needs rewrite
    rw [show e + 1 + 1 = e + 2 from by ring]
    apply stepStar_trans (ih (a + 1) c (e + 2))
    ring_nf; finish

-- Phase 1+2: (n+2, 0, 0, 0, 3n+3) →* (0, 2n+2, 0, n+2, 1)
theorem phase12 (n : ℕ) : ⟨n + 2, 0, 0, 0, 3 * n + 3⟩ [fm]⊢* ⟨0, 2 * n + 2, 0, n + 2, 1⟩ := by
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_trans (r3_drain (n + 2) 0 (3 * n + 3) (a := 0))
  rw [show 0 + (n + 2) = n + 2 from by ring,
      show 3 * n + 3 + (n + 2) = 1 + 2 * (2 * n + 2) from by ring]
  apply stepStar_trans (r4_drain (2 * n + 2) 0 1 (d := n + 2))
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring]
  finish

-- Phase 3: R5+R1+R2. (0, 2n+2, 0, n+2, 1) →* (2, 2n+1, 1, n, 2)
theorem phase3 (n : ℕ) : ⟨0, 2 * n + 2, 0, n + 2, 1⟩ [fm]⊢* ⟨2, 2 * n + 1, 1, n, 2⟩ := by
  rw [show n + 2 = n + 1 + 1 from by ring]
  step fm
  rw [show 2 * n + 2 = 2 * n + 1 + 1 from by ring]
  step fm; step fm; finish

-- Phase 4: R1,R1,R2 chain + R1. (2, 2n+1, 1, n, 2) →* (1, 0, n+2, 0, n+2)
theorem phase4 (n : ℕ) : ⟨2, 2 * n + 1, 1, n, 2⟩ [fm]⊢* ⟨1, 0, n + 2, 0, n + 2⟩ := by
  apply stepStar_trans (r1r1r2_chain n 1 2)
  rw [show 1 + n = n + 1 from by ring, show 2 + n = n + 1 + 1 from by ring]
  step fm; finish

-- Phase 5: R3+R2 chain. (1, 0, n+2, 0, n+2) →⁺ (n+3, 0, 0, 0, 3n+6)
theorem phase5 (n : ℕ) : ⟨1, 0, n + 2, 0, n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 3 * n + 6⟩ := by
  rw [show n + 2 = n + 1 + 1 from by ring]
  step fm; step fm
  -- After R3+R2: (2, 0, n+1, 0, e') for some normalized e'
  -- The expression is (0+2, 0, n+1, 0, n+1+1+1+1) after step
  rw [show n + 1 + 1 + 1 + 1 = n + 4 from by ring,
      show (n + 1 : ℕ) = 0 + (n + 1) from by ring]
  apply stepStar_trans (r3r2_chain (n + 1) 1 0 (n + 4))
  ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, 3n+3) ⊢⁺ (n+3, 0, 0, 0, 3n+6)
theorem main_trans (n : ℕ) : ⟨n + 2, 0, 0, 0, 3 * n + 3⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 3 * n + 6⟩ := by
  apply stepStar_stepPlus_stepPlus (phase12 n)
  apply stepStar_stepPlus_stepPlus (phase3 n)
  apply stepStar_stepPlus_stepPlus (phase4 n)
  exact phase5 n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩)
  · execute fm 4
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, 3 * n + 3⟩) 0
  intro n; exists n + 1; exact main_trans n

end Sz22_2003_unofficial_1158
