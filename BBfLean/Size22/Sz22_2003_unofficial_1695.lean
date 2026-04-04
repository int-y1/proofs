import BBfLean.FM

/-!
# sz22_2003_unofficial #1695: [77/15, 9/154, 14/3, 5/7, 33/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1 -1
 1 -1  0  1  0
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1695

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
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

-- R2/R1/R1 chain: drains a and c while building d and e
theorem r2r1r1_chain : ∀ k : ℕ, ∀ d : ℕ,
    ⟨k + 1, 0, 2 * k + 1, d + 1, d + 2⟩ [fm]⊢* ⟨(1 : ℕ), 0, 1, d + k + 1, d + k + 2⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  step fm; step fm; step fm
  apply stepStar_trans (ih (d + 1))
  have h1 : d + 1 + k + 1 = d + (k + 1) + 1 := by omega
  have h2 : d + 1 + k + 2 = d + (k + 1) + 2 := by omega
  rw [h1, h2]; finish

theorem full_cycle (n : ℕ) : ⟨1, 0, 0, n + 1, n + 1⟩ [fm]⊢⁺ ⟨(1 : ℕ), 0, 0, n + 2, n + 2⟩ := by
  step fm
  have h2 := r3r2_chain n 1 n
  rw [show (1 : ℕ) + n + 1 = n + 2 from by omega] at h2
  apply stepStar_trans h2
  have h3 := r3_chain (n + 2) 0 n
  rw [show (0 : ℕ) + (n + 2) = n + 2 from by omega,
      show n + (n + 2) = 2 * n + 2 from by omega] at h3
  apply stepStar_trans h3
  have h4 := d_to_c (2 * n + 2) (n + 2) 0
  rw [show (0 : ℕ) + (2 * n + 2) = 2 * n + 2 from by omega] at h4
  apply stepStar_trans h4
  step fm; step fm
  have h6 := r2r1r1_chain n 0
  rw [show (0 : ℕ) + 1 = 1 from by omega,
      show (0 : ℕ) + 2 = 2 from by omega,
      show (0 : ℕ) + n + 1 = n + 1 from by omega,
      show (0 : ℕ) + n + 2 = n + 2 from by omega] at h6
  apply stepStar_trans h6
  step fm; step fm; step fm; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, n + 1, n + 1⟩) 0
  intro n; exists n + 1; exact full_cycle n

end Sz22_2003_unofficial_1695
