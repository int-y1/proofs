import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #498: [28/15, 3/22, 25/2, 121/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  2
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_498

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 repeated: convert a to c (b=0, e=0)
theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: convert d to e
theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2,R1 interleaved chain
theorem r2r1_chain : ∀ k, ∀ i c m, ⟨i+1, 0, c+k, i, m+k⟩ [fm]⊢* ⟨i+k+1, 0, c, i+k, m⟩ := by
  intro k; induction' k with k h <;> intro i c m
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show m + (k + 1) = (m + k) + 1 from by ring]
  step fm  -- R2
  step fm  -- R1
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Combined: R5 + R1 + R2R1 chain (⊢*)
theorem r5_r1_chain (a : ℕ) : ⟨0, 0, 2*a+2, 0, 2*a⟩ [fm]⊢* ⟨2*a+2, 0, 0, 2*a+1, 0⟩ := by
  rw [show 2*a+2 = (2*a+1) + 1 from by ring]
  step fm  -- R5: (0, 1, 2*a+1, 0, 2*a)
  rw [show 2*a+1 = 2*a + 1 from by ring]
  step fm  -- R1: (2, 0, 2*a, 1, 2*a)
  have h := r2r1_chain (2*a) 1 0 0
  simp only [Nat.zero_add] at h
  rw [show 1 + 2 * a + 1 = 2 * a + 2 from by ring,
      show 1 + 2 * a = 2 * a + 1 from by ring] at h
  exact h

-- Main transition: (a+1, 0, 0, a, 0) ⊢⁺ (2*a+2, 0, 0, 2*a+1, 0)
theorem main_trans (a : ℕ) : ⟨a+1, 0, 0, a, 0⟩ [fm]⊢⁺ ⟨2*a+2, 0, 0, 2*a+1, 0⟩ := by
  -- First step: R3: (a+1, 0, 0, a, 0) -> (a, 0, 2, a, 0)
  step fm
  -- Now at (a, 0, 2, a, 0), goal is ⊢*
  -- Phase 1: remaining R3 chain
  apply stepStar_trans (c₂ := ⟨0, 0, 2*a+2, a, 0⟩)
  · have h := a_to_c a 0 2 a
    simp only [Nat.zero_add, (by ring : 2 + 2 * a = 2 * a + 2)] at h
    exact h
  -- Phase 2: R4 chain
  apply stepStar_trans (c₂ := ⟨0, 0, 2*a+2, 0, 2*a⟩)
  · have h := d_to_e a (2*a+2) 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 3: R5 + R1 + R2R1 chain
  exact r5_r1_chain a

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun a ↦ ⟨a+2, 0, 0, a+1, 0⟩) 0
  intro a; exists 2*a+2
  show ⟨a+2, 0, 0, a+1, 0⟩ [fm]⊢⁺ ⟨2*a+4, 0, 0, 2*a+3, 0⟩
  have h := main_trans (a+1)
  simp only [(by ring : a + 1 + 1 = a + 2),
             (by ring : 2 * (a + 1) + 2 = 2 * a + 4),
             (by ring : 2 * (a + 1) + 1 = 2 * a + 3)] at h
  exact h

end Sz22_2003_unofficial_498
