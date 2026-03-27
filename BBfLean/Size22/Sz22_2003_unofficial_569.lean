import BBfLean.FM

/-!
# sz22_2003_unofficial #569: [35/6, 1/385, 4/5, 121/2, 45/11]

Vector representation:
```
-1 -1  1  1  0
 0  0 -1 -1 -1
 2  0 -1  0  0
-1  0  0  0  2
 0  2  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_569

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | _ => none

-- R4 repeated: convert a to e
theorem r4_chain (d : ℕ) : ∀ k a e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by omega]
  step fm
  apply stepStar_trans (ih _ _)
  rw [show e + 2 + 2 * k = e + 2 * (k + 1) from by omega]; finish

-- R5+R2 repeated: convert d and e to b
theorem r5r2_chain (e : ℕ) : ∀ k b d, ⟨0, b, 0, d+k, e+2*k⟩ [fm]⊢* ⟨0, b+2*k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by omega,
      show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by omega]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  rw [show b + 2 + 2 * k = b + 2 * (k + 1) from by omega]; finish

-- R3+R1+R1 repeated: transfer b to c and d
theorem r3r1r1_chain (b : ℕ) :
    ∀ k c d, ⟨0, b+2*k, c+1, d, 0⟩ [fm]⊢* ⟨0, b, c+k+1, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; exists 0
  rw [show b + 2 * (k + 1) = b + 2 * k + 1 + 1 from by omega]
  step fm; step fm; step fm
  rw [show c + 1 + 1 = (c + 1) + 1 from by omega,
      show d + 2 = d + 1 + 1 from by omega]
  apply stepStar_trans (ih _ _)
  rw [show c + 1 + k + 1 = c + (k + 1) + 1 from by omega,
      show d + 1 + 1 + 2 * k = d + 2 * (k + 1) from by omega]; finish

-- R3 repeated: convert c to a
theorem r3_chain (d : ℕ) : ∀ k c a, ⟨a, 0, c+k, d, 0⟩ [fm]⊢* ⟨a+2*k, 0, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c a
  · simp; exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega]
  step fm
  apply stepStar_trans (ih _ _)
  rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by omega]; finish

-- Main transition: (d+2, 0, 0, d+1, 0) →⁺ (2*d+4, 0, 0, 2*d+3, 0)
theorem main_trans (d : ℕ) : ⟨d+2, 0, 0, d+1, 0⟩ [fm]⊢⁺ ⟨2*d+4, 0, 0, 2*d+3, 0⟩ := by
  -- Phase 1: R4 chain
  have h1 := r4_chain (d + 1) (d + 2) 0 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R5+R2 chain
  have h2 := r5r2_chain 2 (d + 1) 0 0
  simp only [Nat.zero_add] at h2
  rw [show 2 * (d + 2) = 2 + 2 * (d + 1) from by omega]
  apply stepStar_stepPlus_stepPlus h2
  -- Phase 3: 5 fixed steps (R5, R3, R1, R1, R2)
  step fm; step fm; step fm; step fm; step fm
  -- Phase 4: R3+R1+R1 chain
  have h3 := r3r1r1_chain 0 (d + 1) 0 1
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- Phase 5: R3 chain
  have h4 := r3_chain (1 + 2 * (d + 1)) (d + 1 + 1) 0 0
  simp only [Nat.zero_add] at h4
  have key1 : 1 + 2 * (d + 1) = 2 * d + 3 := by omega
  have key2 : 2 * (d + 1 + 1) = 2 * d + 4 := by omega
  rw [key1]; rw [key1, key2] at h4; exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d, q = ⟨d+2, 0, 0, d+1, 0⟩)
  · intro c ⟨d, hq⟩; subst hq
    refine ⟨⟨2*d+4, 0, 0, 2*d+3, 0⟩, ⟨2*d+2, ?_⟩, main_trans d⟩
    simp only [show 2 * d + 2 + 2 = 2 * d + 4 from by omega,
               show 2 * d + 2 + 1 = 2 * d + 3 from by omega]
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_569
