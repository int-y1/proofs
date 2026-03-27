import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #461: [28/15, 18/7, 1/6, 25/2, 6/5]

Vector representation:
```
 2 -1 -1  1
 1  2  0 -1
-1 -1  0  0
-1  0  2  0
 1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_461

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+1⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a+1, b+2, c, d⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a+1, b+1, c, d⟩
  | _ => none

-- R4 chain: (a+k, 0, c, 0) →* (a, 0, c+2*k, 0)
theorem r4_chain : ∀ k a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R1,R1,R2 interleaved chain
theorem r1r1r2_chain : ∀ k a c d, ⟨a, 2, c+2*k, d⟩ [fm]⊢* ⟨a+5*k, 2, c, d+k⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R2 chain: (a, b, 0, d+k) →* (a+k, b+2*k, 0, d)
theorem r2_chain : ∀ k a b d, ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a+k, b+2*k, 0, d⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R3 chain: (a+k, b+k, c, d) →* (a, b, c, d) when c=0, d=0
theorem r3_chain : ∀ k a b, ⟨a+k, b+k, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- Combined phases 2-5: (0, 0, 2*n+4, 0) →⁺ (4*n+6, 0, 0, 0)
theorem phases2to5 (n : ℕ) : ⟨0, 0, 2*n+4, 0⟩ [fm]⊢⁺ ⟨4*n+6, 0, 0, 0⟩ := by
  -- Phase 2: R5 step
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 2 * n + 4, 0⟩ = some ⟨1, 1, 2 * n + 3, 0⟩; rfl
  -- R1 step
  step fm
  -- R2 step
  step fm
  -- Now at (4, 2, 2*n+2, 0)
  rw [show 2 * n + 2 = 2 + 2 * n from by ring]
  -- Phase 3: R1,R1,R2 chain (n rounds)
  apply stepStar_trans (c₂ := ⟨4+5*n, 2, 2, n⟩)
  · have h := r1r1r2_chain n 4 2 0
    simp only [Nat.zero_add] at h; exact h
  -- Last two R1 steps
  step fm; step fm
  -- Now at (4+5*n+2+2, 0, 0, n+2) which is (5*n+8, 0, 0, n+2)
  -- Phase 4: R2 chain
  apply stepStar_trans (c₂ := ⟨6*n+10, 2*n+4, 0, 0⟩)
  · rw [show 4 + 5 * n + 2 + 2 = 5 * n + 8 from by ring]
    have h := r2_chain (n+2) (5*n+8) 0 0
    simp only [Nat.zero_add,
               (by ring : 5 * n + 8 + (n + 2) = 6 * n + 10),
               (by ring : 0 + 2 * (n + 2) = 2 * n + 4)] at h; exact h
  -- Phase 5: R3 chain
  have h := r3_chain (2*n+4) (4*n+6) 0
  simp only [(by ring : 4 * n + 6 + (2 * n + 4) = 6 * n + 10),
             (by ring : 0 + (2 * n + 4) = 2 * n + 4)] at h; exact h

-- Main transition: (n+2, 0, 0, 0) ⊢⁺ (4*n+6, 0, 0, 0)
theorem main_trans (n : ℕ) : ⟨n+2, 0, 0, 0⟩ [fm]⊢⁺ ⟨4*n+6, 0, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (n+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  rw [show 2 * (n + 2) = 2 * n + 4 from by ring]
  exact phases2to5 n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+2, 0, 0, 0⟩) 0
  intro n; exists 4*n+4; exact main_trans n

end Sz22_2003_unofficial_461
