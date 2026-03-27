import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #36: [1/15, 3/77, 686/3, 5/49, 363/2]

Vector representation:
```
 0 -1 -1  0  0
 0  1  0 -1 -1
 1 -1  0  3  0
 0  0  1 -2  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_36

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+3, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

-- R3 chain: drain b, accumulate a and d (b=0, c=0, e=0)
theorem r3_chain : ∀ k, ∀ a b d, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k, b, 0, d+3*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R4 chain: convert d pairs to c (b=0, e=0)
theorem d_to_c : ∀ k, ∀ a c d, ⟨a, 0, c, d + 2*k, 0⟩ [fm]⊢* ⟨a, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [Nat.mul_succ, ← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5/R1 chain: drain a and c, accumulate e (b=0, d=0)
theorem r5r1_chain : ∀ k, ∀ a e, ⟨a+k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [← Nat.add_assoc]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Interleaved R2/R3 phase: (A, B, 0, 3, E) →* (A+B+E, 0, 0, 3*B+2*E+3, 0)
theorem r2r3_phase : ∀ E, ∀ A B, ⟨A, B, 0, 3, E⟩ [fm]⊢* ⟨A+B+E, 0, 0, 3*B+2*E+3, 0⟩ := by
  intro E; induction' E using Nat.strongRecOn with E ih; intro A B
  rcases E with _ | _ | _ | E'
  · -- E=0: R3 chain drains b
    rw [show B = 0 + B from by ring]
    apply stepStar_trans (r3_chain B A 0 3)
    ring_nf; finish
  · -- E=1: one R2, then R3 chain
    step fm
    rw [show B + 1 = 0 + (B + 1) from by ring]
    apply stepStar_trans (r3_chain (B+1) A 0 2)
    ring_nf; finish
  · -- E=2: two R2s, then R3 chain
    step fm; step fm
    rw [show B + 1 + 1 = 0 + (B + 2) from by ring]
    apply stepStar_trans (r3_chain (B+2) A 0 1)
    ring_nf; finish
  · -- E=E'+3: three R2s, one R3, then recurse
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih E' (by omega) _ _)
    ring_nf; finish

-- Phase 4a: 4 steps from (a+2, 0, a+2, 1, 0) to (a+1, 0, a, 0, 1)
theorem phase4a (a : ℕ) : ⟨a+2, 0, a+2, 1, 0⟩ [fm]⊢* ⟨a+1, 0, a, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Main transition: (1,0,0,0,e) →⁺ (1,0,0,0,2*e+3)
theorem main_trans (e : ℕ) : ⟨1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨1, 0, 0, 0, 2*e+3⟩ := by
  -- Phase 1: R5, R3 → (1,0,0,3,e+2)
  step fm; step fm
  -- Phase 2: interleaved R2/R3 → (e+3, 0, 0, 2e+7, 0)
  apply stepStar_trans (r2r3_phase (e+2) 1 0)
  -- Phase 3: R4 chain → (e+3, 0, e+3, 1, 0)
  rw [show 3 * 0 + 2 * (e + 2) + 3 = 1 + 2 * (e + 3) from by ring]
  rw [show 1 + 0 + (e + 2) = e + 3 from by ring]
  apply stepStar_trans (d_to_c (e+3) (e+3) 0 1)
  simp only [Nat.zero_add]
  -- Phase 4a: 4 steps → (e+2, 0, e+1, 0, 1)
  rw [show e + 3 = (e + 1) + 2 from by ring]
  apply stepStar_trans (phase4a (e+1))
  rw [show e + 1 + 1 = e + 2 from by ring]
  -- Phase 4b: R5/R1 chain → (1, 0, 0, 0, 2e+3)
  rw [show e + 2 = 1 + (e + 1) from by ring]
  apply stepStar_trans (r5r1_chain (e+1) 1 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨1, 0, 0, 0, e⟩) 0
  intro e; exact ⟨2*e+3, main_trans e⟩

end Sz22_2003_unofficial_36
