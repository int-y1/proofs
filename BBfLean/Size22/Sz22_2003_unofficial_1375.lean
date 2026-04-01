import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1375: [63/10, 5/33, 14/3, 11/49, 15/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -2  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1375

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: drain d by 2s into e. Requires b=0, c=0.
theorem r4_chain : ∀ k a e, ⟨a, 0, 0, 2 * k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- R3 chain: drain b into a and d. Requires c=0, e=0.
theorem r3_chain : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

-- R2 chain: drain b and e into c. Requires a=0 (so R1 doesn't fire).
theorem r2_chain : ∀ k b c d, ⟨0, b + k, c, d, k⟩ [fm]⊢* ⟨0, b, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) d)
    ring_nf; finish

-- R1+R3 interleave: each round R1 then R3.
-- Net effect per round: b+=1, c-=1, d+=2.
theorem r1r3_chain : ∀ k b d, ⟨1, b, k, d, 0⟩ [fm]⊢* ⟨1, b + k, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (b + 1) (d + 2))
    ring_nf; finish

-- R2+R1 interleave: each round R2 then R1.
-- Net effect per round: a-=1, b+=1, d+=1, e-=1.
-- First component is k (counts down to 0).
theorem r2r1_chain : ∀ k b d e, ⟨k, b + 1, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k + 1, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) (d + 1) e)
    ring_nf; finish

-- Middle phase: from (n, 3, 0, 1, 2*n+2) to (1, 0, n+2, n+2, 0)
-- Decomposed as: r2r1_chain + r2_chain + R3 step
theorem middle_phase : ∀ n, ⟨n, 3, 0, 1, 2 * n + 2⟩ [fm]⊢* ⟨1, 0, n + 2, n + 2, 0⟩ := by
  intro n
  rw [show 2 * n + 2 = (n + 2) + n from by ring]
  apply stepStar_trans (r2r1_chain n 2 1 (n + 2))
  rw [show 2 + n + 1 = 1 + (n + 2) from by ring,
      show 1 + n = n + 1 from by ring]
  apply stepStar_trans (r2_chain (n + 2) 1 0 (n + 1))
  rw [show 0 + (n + 2) = n + 2 from by ring]
  step fm; finish

-- Main transition: (n+2, 0, 0, 4*n+4, 0) →⁺ (n+3, 0, 0, 4*n+8, 0)
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 4 * n + 4, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 4 * n + 8, 0⟩ := by
  -- Phase 1: R4 drain
  rw [show 4 * n + 4 = 2 * (2 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * n + 2) (n + 2) 0)
  rw [show 0 + (2 * n + 2) = 2 * n + 2 from by ring]
  -- Phase 2: R5 + R1
  step fm
  step fm
  -- Phase 3: Middle phase
  apply stepStar_trans (middle_phase n)
  -- Phase 4: R1+R3 interleave
  apply stepStar_trans (r1r3_chain (n + 2) 0 (n + 2))
  rw [show 0 + (n + 2) = n + 2 from by ring,
      show n + 2 + 2 * (n + 2) = 3 * n + 6 from by ring]
  -- Phase 5: R3 chain
  apply stepStar_trans (r3_chain (n + 2) 1 (3 * n + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 4, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 4 * n + 4, 0⟩) 0
  intro n
  exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1375
