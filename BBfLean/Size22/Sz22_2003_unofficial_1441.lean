import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1441: [7/15, 242/3, 9/385, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  2 -1 -1 -1
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1441

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: transfer e to c (b=0, d=0 so R1-R3 don't fire)
theorem e_to_c : ∀ k a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

-- 4-step round draining d: R4, R3, R2, R2
-- (a, 0, 0, d+k, e+2) ⊢* (a+2k, 0, 0, d, e+2+2k)
theorem d_drain : ∀ k, ∀ a d e, ⟨a, 0, 0, d + k, e + 2⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e + 2 + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 2 = (e + 1) + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) d (e + 2)); ring_nf; finish

-- 5-step drain chain: R5, R1, R3, R1, R1
-- (a+k, 0, c+4k, d, 0) ⊢* (a, 0, c, d+2k, 0)
theorem c_drain : ∀ k, ∀ a c d, ⟨a + k, 0, c + 4 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · -- State: ((a+k)+1, 0, c+4k+4, d, 0)
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 4 * (k + 1) = c + 4 * k + 3 + 1 from by ring]
    step fm -- R5: (a+k, 1, c+4k+3+1, d, 1)
    -- For R1, need (a, b+1, c+1, d, e): b+1 = 1 ✓, need c+1 form
    rw [show c + 4 * k + 3 + 1 = (c + 4 * k + 3) + 1 from by ring]
    step fm -- R1: (a+k, 0, c+4k+3, d+1, 1)
    -- For R3, need (a, b, c+1, d+1, e+1): c+1 form, d+1 form, e+1 form
    rw [show c + 4 * k + 3 = (c + 4 * k + 2) + 1 from by ring]
    step fm -- R3: (a+k, 2, c+4k+2, d, 0)
    -- For R1, need (a, b+1, c+1, d, e): b+1 = 2 ✓ (b=1), need c+1 form
    rw [show c + 4 * k + 2 = (c + 4 * k + 1) + 1 from by ring]
    step fm -- R1: (a+k, 1, c+4k+1, d+1, 0)
    -- For R1, need (a, b+1, c+1, d, e): b+1 = 1 ✓, need c+1 form
    rw [show c + 4 * k + 1 = (c + 4 * k) + 1 from by ring]
    step fm -- R1: (a+k, 0, c+4k, d+2, 0)
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- Drain c=3: (a+1, 0, 3, d, 0) ⊢* (a+1, 0, 0, d+1, 2)
-- via R5, R1, R3, R1, R2
theorem c3_drain (a d : ℕ) : ⟨a + 1, 0, 3, d, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, d + 1, 2⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Main transition: (a+1, 0, 0, 2*(n+1), 0) ⊢⁺ (a+6*n+8, 0, 0, 2*(n+2), 0)
theorem main_trans (a n : ℕ) :
    ⟨a + 1, 0, 0, 2 * (n + 1), 0⟩ [fm]⊢⁺ ⟨a + 6 * n + 8, 0, 0, 2 * (n + 2), 0⟩ := by
  -- Phase 1: Opening (R5, R2)
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring]
  step fm; step fm
  -- State: (a+1, 0, 0, 2*(n+1), 3)
  rw [show 2 * n + 1 + 1 = 0 + (2 * n + 2) from by ring]
  -- Phase 2: D-drain, 2*(n+1) rounds
  apply stepStar_trans (d_drain (2 * n + 2) (a + 1) 0 1)
  rw [show a + 1 + 2 * (2 * n + 2) = a + 4 * n + 5 from by ring,
      show 1 + 2 + 2 * (2 * n + 2) = 0 + (4 * n + 7) from by ring]
  -- State: (a+4n+5, 0, 0, 0, 4n+7)
  -- Phase 3: E-to-C
  apply stepStar_trans (e_to_c (4 * n + 7) (a + 4 * n + 5) 0 0)
  rw [show 0 + (4 * n + 7) = 4 * (n + 1) + 3 from by ring]
  -- State: (a+4n+5, 0, 4(n+1)+3, 0, 0)
  -- Phase 4: C-drain, n+1 times. c=4(n+1)+3 -> c=3, d=0 -> d=2(n+1)
  rw [show a + 4 * n + 5 = (a + 3 * n + 4) + (n + 1) from by ring,
      show 4 * (n + 1) + 3 = 3 + 4 * (n + 1) from by ring]
  apply stepStar_trans (c_drain (n + 1) (a + 3 * n + 4) 3 0)
  rw [show 0 + 2 * (n + 1) = 2 * n + 2 from by ring]
  -- State: (a+3n+4, 0, 3, 2n+2, 0)
  -- Phase 5: C3-drain
  rw [show a + 3 * n + 4 = (a + 3 * n + 3) + 1 from by ring]
  apply stepStar_trans (c3_drain (a + 3 * n + 3) (2 * n + 2))
  rw [show a + 3 * n + 3 + 1 = a + 3 * n + 4 from by ring]
  -- State: (a+3n+4, 0, 0, 2n+3, 2)
  rw [show 2 * n + 2 + 1 = 0 + (2 * n + 3) from by ring]
  -- Phase 6: D-drain-2, 2n+3 rounds
  apply stepStar_trans (d_drain (2 * n + 3) (a + 3 * n + 4) 0 0)
  rw [show a + 3 * n + 4 + 2 * (2 * n + 3) = a + 7 * n + 10 from by ring,
      show 0 + 2 + 2 * (2 * n + 3) = 0 + (4 * n + 8) from by ring]
  -- State: (a+7n+10, 0, 0, 0, 4n+8)
  -- Phase 7: E-to-C
  apply stepStar_trans (e_to_c (4 * n + 8) (a + 7 * n + 10) 0 0)
  rw [show 0 + (4 * n + 8) = 4 * (n + 2) from by ring]
  -- State: (a+7n+10, 0, 4(n+2), 0, 0)
  -- Phase 8: C-drain-final, n+2 times. c=4(n+2) -> c=0, d=0 -> d=2(n+2)
  rw [show a + 7 * n + 10 = (a + 6 * n + 8) + (n + 2) from by ring,
      show 4 * (n + 2) = 0 + 4 * (n + 2) from by ring]
  apply stepStar_trans (c_drain (n + 2) (a + 6 * n + 8) 0 0)
  rw [show 0 + 2 * (n + 2) = 2 * (n + 2) from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩)
  · execute fm 23
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, n⟩ ↦ ⟨a + 1, 0, 0, 2 * (n + 1), 0⟩) ⟨1, 0⟩
  intro ⟨a, n⟩; exact ⟨⟨a + 6 * n + 7, n + 1⟩, main_trans a n⟩

end Sz22_2003_unofficial_1441
