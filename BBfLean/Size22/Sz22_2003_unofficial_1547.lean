import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1547: [7/30, 44/21, 9/2, 5/11, 7/3]

Vector representation:
```
-1 -1 -1  1  0
 2 -1  0 -1  1
-1  2  0  0  0
 0  0  1  0 -1
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1547

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R3 chain: drain a, filling b (c=0, d=0, so R3 fires).
theorem r3_chain : ∀ k a b, ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2)); ring_nf; finish

-- R4 chain: drain e, filling c (a=0, d=0).
theorem r4_chain : ∀ k c, ⟨0, b, c, 0, k⟩ [fm]⊢* ⟨0, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · simp; exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- R2 chain: drain b and d, filling a and e (c=0).
theorem r2_chain : ∀ k a b d e, ⟨a, b + k, 0, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b d (e + 1)); ring_nf; finish

-- R1R1R2 chain: three-step rounds (R1, R1, R2) draining c by 2 each round.
theorem r1r1r2_chain : ∀ k b c d e,
    ⟨2, b + 3 * k, c + 2 * k, d, e⟩ [fm]⊢* ⟨2, b, c, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; exists 0
  · rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show (b + 3 * k) + 3 = ((b + 3 * k) + 2) + 1 from by ring,
        show (c + 2 * k) + 2 = ((c + 2 * k) + 1) + 1 from by ring]
    step fm
    rw [show (b + 3 * k) + 2 = ((b + 3 * k) + 1) + 1 from by ring]
    step fm
    rw [show d + 1 + 1 = d + 2 from by ring,
        show (b + 3 * k) + 1 = (b + 3 * k) + 1 from rfl]
    step fm
    apply stepStar_trans (ih b c (d + 1) (e + 1)); ring_nf; finish

-- Even case: n = 2*m, canonical (2*m+2, 0, 0, 0, 2*m+1) ⊢⁺ (2*m+3, 0, 0, 0, 2*m+2)
theorem main_even (m : ℕ) :
    ⟨2 * m + 2, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨2 * m + 3, 0, 0, 0, 2 * m + 2⟩ := by
  -- Phase 1: R3 chain
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * m + 2) 0 0 (e := 2 * m + 1))
  rw [show 0 + 2 * (2 * m + 2) = 4 * m + 4 from by ring]
  -- Phase 2: R4 chain
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 1) 0 (b := 4 * m + 4))
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  -- Phase 3: R5 step
  rw [show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
  step fm
  -- Phase 4: R2 step
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- Phase 5: R1R1R2 chain (m rounds)
  rw [show 4 * m + 2 = (m + 2) + 3 * m from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r1r1r2_chain m (m + 2) 1 0 1)
  -- Phase 6: R1 step (c=1)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show m + 2 = (m + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- Phase 7: R2 chain (m+1 steps)
  rw [show m + 1 = 0 + (m + 1) from by ring,
      show 0 + m + 1 = 0 + (m + 1) from by ring,
      show 1 + m = m + 1 from by ring]
  apply stepStar_trans (r2_chain (m + 1) 1 0 0 (m + 1))
  ring_nf; finish

-- Odd case: n = 2*m+1, canonical (2*m+3, 0, 0, 0, 2*m+2) ⊢⁺ (2*m+4, 0, 0, 0, 2*m+3)
theorem main_odd (m : ℕ) :
    ⟨2 * m + 3, 0, 0, 0, 2 * m + 2⟩ [fm]⊢⁺ ⟨2 * m + 4, 0, 0, 0, 2 * m + 3⟩ := by
  -- Phase 1: R3 chain
  rw [show 2 * m + 3 = 0 + (2 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * m + 3) 0 0 (e := 2 * m + 2))
  rw [show 0 + 2 * (2 * m + 3) = 4 * m + 6 from by ring]
  -- Phase 2: R4 chain
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 2) 0 (b := 4 * m + 6))
  rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring]
  -- Phase 3: R5 step
  rw [show 4 * m + 6 = (4 * m + 5) + 1 from by ring]
  step fm
  -- Phase 4: R2 step
  rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  -- Phase 5: R1R1R2 chain (m+1 rounds) + R2 chain (m+1 steps)
  rw [show 4 * m + 4 = (m + 1) + 3 * (m + 1) from by ring,
      show 2 * m + 2 = 0 + 2 * (m + 1) from by ring]
  apply stepStar_trans (r1r1r2_chain (m + 1) (m + 1) 0 0 1)
  rw [show 0 + (m + 1) = m + 1 from by ring,
      show 1 + (m + 1) = m + 2 from by ring,
      show (m + 1 : ℕ) = 0 + (m + 1) from by ring]
  apply stepStar_trans (r2_chain (m + 1) 2 0 0 (m + 2))
  ring_nf; finish

-- Combined transition: (n+2, 0, 0, 0, n+1) ⊢⁺ (n+3, 0, 0, 0, n+2)
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, n + 2⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact main_even m
  · subst hm
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show 2 * m + 1 + 3 = 2 * m + 4 from by ring]
    exact main_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 0, n + 1⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1547
