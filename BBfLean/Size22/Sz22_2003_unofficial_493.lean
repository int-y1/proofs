import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #493: [28/15, 3/22, 25/2, 11/7, 3/5, 1/3]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  1
 0  1 -1  0  0
 0 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_493

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- R3 chain: drain a, produce 2c per step
theorem a_to_c : ∀ k a c d, ⟨a + k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R4 chain: drain d, produce e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R1R2 interleaved chain: k rounds of (R1, R2)
theorem r1r2_chain : ∀ k a c d e, ⟨a, 1, c + k, d, e + k⟩ [fm]⊢* ⟨a + k, 1, c, d + k, e⟩ := by
  intro k; induction' k with k h <;> intro a c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _ _ _); ring_nf; finish

-- Main transition: (n+2, 0, c, n+1, 0) ⊢⁺ (n+3, 0, c+n+1, n+2, 0)
theorem main_trans (n c : ℕ) : ⟨n + 2, 0, c, n + 1, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, c + n + 1, n + 2, 0⟩ := by
  -- Phase 1 (⊢*): R3 chain drains a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, c + 2 * (n + 2), n + 1, 0⟩)
  · have h := a_to_c (n + 2) 0 c (n + 1)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: first R4 step (⊢), then remaining R4 steps (⊢*)
  apply step_stepStar_stepPlus (c₂ := ⟨0, 0, c + 2 * (n + 2), n, 1⟩)
  · show fm ⟨0, 0, c + 2 * (n + 2), n + 0 + 1, 0⟩ = some ⟨0, 0, c + 2 * (n + 2), n + 0, 0 + 1⟩
    rfl
  apply stepStar_trans (c₂ := ⟨0, 0, c + 2 * (n + 2), 0, n + 1⟩)
  · have h := d_to_e n (c + 2 * (n + 2)) 0 1
    simp only [Nat.zero_add, Nat.add_comm 1 n] at h; exact h
  -- Phase 3: R5 step
  rw [show c + 2 * (n + 2) = (c + n + 2) + (n + 1) + 1 from by ring]
  step fm
  -- Phase 4: R1R2 chain
  apply stepStar_trans (c₂ := ⟨n + 1, 1, c + n + 2, n + 1, 0⟩)
  · have h := r1r2_chain (n + 1) 0 (c + n + 2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 5: final R1 step
  rw [show c + n + 2 = (c + n + 1) + 1 from by ring]
  step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, c⟩ ↦ ⟨n + 2, 0, c, n + 1, 0⟩) ⟨0, 0⟩
  intro ⟨n, c⟩; exact ⟨⟨n + 1, c + n + 1⟩, main_trans n c⟩

end Sz22_2003_unofficial_493
