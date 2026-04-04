import BBfLean.FM

/-!
# sz22_2003_unofficial #1696: [77/15, 9/154, 14/3, 5/7, 9/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1 -1
 1 -1  0  1  0
 0  0  1 -1  0
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1696

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R3/R2 interleaved chain: drains e while b grows
theorem r3r2_chain : ∀ k : ℕ, ∀ b d : ℕ,
    ⟨0, b + 1, 0, d, k⟩ [fm]⊢* ⟨(0 : ℕ), b + k + 1, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  step fm; step fm
  rw [show b + 2 = (b + 1) + 1 from by omega]
  apply stepStar_trans (ih (b + 1) d)
  rw [show b + 1 + k + 1 = b + (k + 1) + 1 from by omega]; finish

-- R3 chain: converts b to a and d
theorem r3_chain : ∀ k : ℕ, ∀ a d : ℕ,
    ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  step fm
  apply stepStar_trans (ih (a + 1) (d + 1))
  have h1 : a + 1 + k = a + (k + 1) := by omega
  have h2 : d + 1 + k = d + (k + 1) := by omega
  rw [h1, h2]; finish

-- R4 chain: converts d to c
theorem d_to_c : ∀ k : ℕ, ∀ a c : ℕ,
    ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  step fm
  apply stepStar_trans (ih a (c + 1))
  have : c + 1 + k = c + (k + 1) := by omega
  rw [this]; finish

-- {R2,R1,R1} chain: k rounds draining a and c while building d and e
theorem r2r1r1_chain : ∀ k : ℕ, ∀ d : ℕ,
    ⟨k + 1, 0, 2 * k, d + 2, d + 2⟩ [fm]⊢* ⟨(1 : ℕ), 0, 0, d + k + 2, d + k + 2⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  step fm; step fm; step fm
  rw [show d + 3 = (d + 1) + 2 from by omega]
  apply stepStar_trans (ih (d + 1))
  rw [show d + 1 + k + 2 = d + (k + 1) + 2 from by omega]; finish

theorem full_cycle (n : ℕ) : ⟨1, 0, 0, n + 2, n + 2⟩ [fm]⊢⁺ ⟨(1 : ℕ), 0, 0, n + 3, n + 3⟩ := by
  -- Phase 0: R2 step
  step fm
  -- Phase 1: R3/R2 interleaved (n+1 times, draining e=n+1)
  have h1 := r3r2_chain (n + 1) 1 (n + 1)
  rw [show (1 : ℕ) + (n + 1) + 1 = n + 3 from by omega] at h1
  apply stepStar_trans h1
  -- Phase 2: R3 chain (n+3 times, draining b=n+3)
  have h2 := r3_chain (n + 3) 0 (n + 1)
  rw [show (0 : ℕ) + (n + 3) = n + 3 from by omega,
      show n + 1 + (n + 3) = 2 * n + 4 from by omega] at h2
  apply stepStar_trans h2
  -- Phase 3: R4 chain (2n+4 times, draining d)
  have h3 := d_to_c (2 * n + 4) (n + 3) 0
  rw [show (0 : ℕ) + (2 * n + 4) = 2 * n + 4 from by omega] at h3
  apply stepStar_trans h3
  -- Phase 4: R5 step
  step fm
  -- Phase 5: R1,R1 (first pair)
  step fm; step fm
  -- Phase 6: {R2,R1,R1} chain
  rw [show 2 * n + 2 = 2 * (n + 1) from by omega]
  have h4 := r2r1r1_chain (n + 1) 0
  rw [show (0 : ℕ) + 2 = 2 from by omega,
      show (0 : ℕ) + (n + 1) + 2 = n + 3 from by omega] at h4
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, n + 2, n + 2⟩) 0
  intro n; exists n + 1; exact full_cycle n

end Sz22_2003_unofficial_1696
