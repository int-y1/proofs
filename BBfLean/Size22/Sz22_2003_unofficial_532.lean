import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #532: [28/15, 39/22, 65/2, 11/7, 21/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  1
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_532

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R3 repeated: drain a into c and f
theorem r3_drain : ∀ k c d f, ⟨k, 0, c, d, 0, f⟩ [fm]⊢* ⟨0, 0, c+k, d, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro c d f
  · exists 0
  rw [show c + (k + 1) = (c + 1) + k from by omega,
      show f + (k + 1) = (f + 1) + k from by omega]
  step fm
  exact h _ _ _

-- R4 repeated: drain d into e
theorem d_to_e : ∀ k c e f, ⟨0, 0, c, k, e, f⟩ [fm]⊢* ⟨0, 0, c, 0, e+k, f⟩ := by
  intro k; induction' k with k h <;> intro c e f
  · exists 0
  rw [show e + (k + 1) = (e + 1) + k from by omega]
  step fm
  exact h _ _ _

-- R1R2 chain: (k+1) rounds consuming c and e simultaneously
theorem r1r2_chain : ∀ k, ∀ a c d e f,
    ⟨a, 1, c+(k+1), d, e+(k+1), f⟩ [fm]⊢* ⟨a+(k+1), 1, c, d+(k+1), e, f+(k+1)⟩ := by
  intro k; induction' k with k h <;> intro a c d e f
  · step fm; step fm; finish
  rw [show c + (k + 1 + 1) = (c + (k + 1)) + 1 from by omega,
      show e + (k + 1 + 1) = (e + (k + 1)) + 1 from by omega]
  step fm; step fm
  -- State: (a+1, 1, c+(k+1), d+1, e+(k+1), f+1)
  apply stepStar_trans (h (a+1) c (d+1) e (f+1))
  -- Result of IH: ((a+1)+(k+1), 1, c, (d+1)+(k+1), e, (f+1)+(k+1))
  rw [show a + 1 + (k + 1) = a + (k + 1 + 1) from by omega,
      show d + 1 + (k + 1) = d + (k + 1 + 1) from by omega,
      show f + 1 + (k + 1) = f + (k + 1 + 1) from by omega]
  finish

-- R2 repeated: drain a and e with c=0 (R1 can't fire since c=0)
theorem r2_drain : ∀ k, ∀ a b d e f,
    ⟨a+k, b, 0, d, e+k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, e, f+k⟩ := by
  intro k; induction' k with k h <;> intro a b d e f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by omega,
      show e + (k + 1) = (e + k) + 1 from by omega]
  step fm
  -- State: (a+k, b+1, 0, d, e+k, f+1)
  apply stepStar_trans (h a (b+1) d e (f+1))
  rw [show b + 1 + k = b + (k + 1) from by omega,
      show f + 1 + k = f + (k + 1) from by omega]
  finish

-- R3R1 chain: interleave R3 and R1, consuming b
theorem r3r1_chain : ∀ k, ∀ a b d f,
    ⟨a+1, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+k+1, b, 0, d+k, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a b d f
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by omega]
  step fm; step fm
  -- State: (a+2, b+k, 0, d+1, 0, f+1) = ((a+1)+1, b+k, 0, d+1, 0, f+1)
  apply stepStar_trans (h (a+1) b (d+1) (f+1))
  rw [show a + 1 + k + 1 = a + (k + 1) + 1 from by omega,
      show d + 1 + k = d + (k + 1) from by omega,
      show f + 1 + k = f + (k + 1) from by omega]
  finish

-- Full cycle: (k+2, 0, 0, 2(k+1), 0, 2k(k+1)) →⁺ (k+3, 0, 0, 2(k+2), 0, 2(k+1)(k+2))
theorem full_cycle (k : ℕ) :
    ⟨k+2, 0, 0, 2*(k+1), 0, 2*k*(k+1)⟩ [fm]⊢⁺ ⟨k+3, 0, 0, 2*(k+2), 0, 2*(k+1)*(k+2)⟩ := by
  -- Phase 1: R3 × (k+2), first step for ⊢⁺
  rw [show k + 2 = (k + 1) + 1 from by omega]
  step fm
  apply stepStar_trans (r3_drain (k+1) 1 (2*(k+1)) (2*k*(k+1)+1))
  -- State: (0, 0, 1+(k+1), 2*(k+1), 0, 2*k*(k+1)+1+(k+1))
  -- Phase 2: R4 × (2*(k+1))
  rw [show 1 + (k + 1) = k + 2 from by omega,
      show 2 * k * (k + 1) + 1 + (k + 1) = 2 * k * k + 3 * k + 2 from by ring]
  apply stepStar_trans (d_to_e (2*(k+1)) (k+2) 0 (2*k*k+3*k+2))
  -- State: (0, 0, k+2, 0, 0+2*(k+1), 2*k*k+3*k+2)
  -- Phase 3: R5
  rw [show 0 + 2 * (k + 1) = 2 * k + 2 from by omega,
      show 2 * k * k + 3 * k + 2 = (2 * k * k + 3 * k + 1) + 1 from by omega]
  step fm
  -- State: (0, 1, k+2, 1, 2*k+2, 2*k*k+3*k+1)
  -- Phase 4: R1R2 × (k+2) rounds [call r1r2_chain with parameter k+1]
  have h4 := r1r2_chain (k+1) 0 0 1 k (2*k*k+3*k+1)
  rw [show 0 + (k + 1 + 1) = k + 2 from by omega,
      show k + (k + 1 + 1) = 2 * k + 2 from by omega,
      show 1 + (k + 1 + 1) = k + 3 from by omega,
      show 2 * k * k + 3 * k + 1 + (k + 1 + 1) = 2 * k * k + 4 * k + 3 from by ring] at h4
  apply stepStar_trans h4
  -- State: (k+2, 1, 0, k+3, k, 2*k*k+4*k+3)
  -- Phase 5: R2 × k rounds
  have h5 := r2_drain k 2 1 (k+3) 0 (2*k*k+4*k+3)
  rw [show 2 + k = k + 2 from by omega,
      show 0 + k = k from by omega,
      show 1 + k = k + 1 from by omega,
      show 2 * k * k + 4 * k + 3 + k = 2 * k * k + 5 * k + 3 from by ring] at h5
  apply stepStar_trans h5
  -- State: (2, k+1, 0, k+3, 0, 2*k*k+5*k+3)
  -- Phase 6: R3R1 × (k+1) rounds
  have h6 := r3r1_chain (k+1) 1 0 (k+3) (2*k*k+5*k+3)
  rw [show 0 + (k + 1) = k + 1 from by omega,
      show 1 + (k + 1) + 1 = k + 3 from by omega,
      show k + 3 + (k + 1) = 2 * (k + 2) from by omega,
      show 2 * k * k + 5 * k + 3 + (k + 1) = 2 * (k + 1) * (k + 2) from by ring] at h6
  exact h6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨k+2, 0, 0, 2*(k+1), 0, 2*k*(k+1)⟩) 0
  intro k; exact ⟨k+1, full_cycle k⟩
