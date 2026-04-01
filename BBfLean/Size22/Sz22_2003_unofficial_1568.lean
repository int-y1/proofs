import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1568: [7/45, 242/5, 5/77, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
 1  0 -1  0  2
 0  0  1 -1 -1
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1568

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R4 chain: move e to b.
theorem r4_chain : ∀ k, ∀ a b, ⟨a, b, 0, 0, k⟩ [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · step fm
    apply stepStar_trans (ih a (b + 1))
    ring_nf; finish

-- R5+R1 chain: each round a -= 1, b -= 2, d += 2.
theorem r5r1_chain : ∀ k, ∀ a b d, ⟨a + k, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by omega,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by omega]
    step fm; step fm
    show ⟨a + k, b + 2 * k, 0, d + 1 + 1, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * (k + 1), 0⟩
    rw [show d + 1 + 1 = d + 2 from by omega,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by omega]
    exact ih a b (d + 2)

-- R3+R2 chain with b=0: (a, 0, 0, k, e+1) ⊢* (a+k, 0, 0, 0, e+k+1)
theorem r3r2_b0 : ∀ k, ∀ a e, ⟨a, 0, 0, k, e + 1⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; step fm
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- R3+R2 chain with b=1: (a, 1, 0, k, e+1) ⊢* (a+k, 1, 0, 0, e+k+1)
theorem r3r2_b1 : ∀ k, ∀ a e, ⟨a, 1, 0, k, e + 1⟩ [fm]⊢* ⟨a + k, 1, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; step fm
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- Main transition: (a+e+2, 0, 0, 0, 2*e+3) ⊢⁺ (a+3*e+8, 0, 0, 0, 2*e+9)
theorem main_trans : ⟨a + e + 2, 0, 0, 0, 2 * e + 3⟩ [fm]⊢⁺ ⟨a + 3 * e + 8, 0, 0, 0, 2 * e + 9⟩ := by
  -- Phase 1: R4 chain (2*e+3 steps): (a+e+2, 2*e+3, 0, 0, 0)
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * e + 3) (a + e + 2) 0)
  rw [show 0 + (2 * e + 3) = 2 * e + 3 from by ring]
  -- Phase 2: R5+R1 chain (e+1 rounds): (a+1, 1, 0, 2*e+2, 0)
  rw [show a + e + 2 = (a + 1) + (e + 1) from by ring,
      show 2 * e + 3 = 1 + 2 * (e + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (e + 1) (a + 1) 1 0)
  rw [show 0 + 2 * (e + 1) = 2 * e + 2 from by ring]
  -- Phase 3: R5 + R2
  rw [show a + 1 = a + 1 from rfl]
  step fm
  rw [show 2 * e + 2 + 1 = 2 * e + 3 from by ring]
  step fm
  -- Phase 4: R3+R2 b=1 (2*e+3 rounds)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_b1 (2 * e + 3) (a + 1) 1)
  rw [show a + 1 + (2 * e + 3) = a + 2 * e + 4 from by ring,
      show 1 + (2 * e + 3) + 1 = 2 * e + 5 from by ring]
  -- Phase 5: R4 chain (2*e+5 steps)
  apply stepStar_trans (r4_chain (2 * e + 5) (a + 2 * e + 4) 1)
  rw [show 1 + (2 * e + 5) = 2 * e + 6 from by ring]
  -- Phase 6: R5+R1 chain (e+3 rounds)
  rw [show a + 2 * e + 4 = (a + e + 1) + (e + 3) from by ring,
      show 2 * e + 6 = 0 + 2 * (e + 3) from by ring]
  apply stepStar_trans (r5r1_chain (e + 3) (a + e + 1) 0 0)
  rw [show 0 + 2 * (e + 3) = 2 * e + 6 from by ring]
  -- Phase 7: R5 + R2
  rw [show a + e + 1 = (a + e) + 1 from by ring]
  step fm
  rw [show 2 * e + 6 + 1 = 2 * e + 7 from by ring]
  step fm
  -- Phase 8: R3+R2 b=0 (2*e+7 rounds)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_b0 (2 * e + 7) (a + e + 1) 1)
  rw [show a + e + 1 + (2 * e + 7) = a + 3 * e + 8 from by ring,
      show 1 + (2 * e + 7) + 1 = 2 * e + 9 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨8, 0, 0, 0, 9⟩) (by execute fm 44)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + e + 2, 0, 0, 0, 2 * e + 3⟩) ⟨3, 3⟩
  intro ⟨a, e⟩
  refine ⟨⟨a + 2 * e + 3, e + 3⟩, ?_⟩
  show ⟨a + e + 2, 0, 0, 0, 2 * e + 3⟩ [fm]⊢⁺ ⟨(a + 2 * e + 3) + (e + 3) + 2, 0, 0, 0, 2 * (e + 3) + 3⟩
  rw [show (a + 2 * e + 3) + (e + 3) + 2 = a + 3 * e + 8 from by ring,
      show 2 * (e + 3) + 3 = 2 * e + 9 from by ring]
  exact main_trans

end Sz22_2003_unofficial_1568
