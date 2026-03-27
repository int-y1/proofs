import BBfLean.FM

/-!
# sz22_2003_unofficial #562: [315/2, 4/55, 7/15, 11/21, 5/7]

Vector representation:
```
-1  2  1  1  0
 2  0 -1  0 -1
 0 -1 -1  1  0
 0 -1  0 -1  1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_562

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R2,R1,R1 chain: k+1 rounds consuming e, building b,c,d
theorem r2r1r1_chain : ∀ k, ∀ b c d,
    ⟨0, b, c+1, d, k+1⟩ [fm]⊢* ⟨0, b+4*k+4, c+k+2, d+2*k+2, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · step fm; step fm; step fm
    rw [show b + 2 + 2 = b + 4 * 0 + 4 from by omega,
        show c + 1 + 1 = c + 0 + 2 from by omega,
        show d + 1 + 1 = d + 2 * 0 + 2 from by omega]
    finish
  rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by omega]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  rw [show b + 2 + 2 + 4 * k + 4 = b + 4 * (k + 1) + 4 from by omega,
      show c + 1 + k + 2 = c + (k + 1) + 2 from by omega,
      show d + 1 + 1 + 2 * k + 2 = d + 2 * (k + 1) + 2 from by omega]
  finish

-- R3 chain: k rounds consuming b and c, building d
theorem r3_chain : ∀ k, ∀ b c d,
    ⟨0, b+k, c+k, d, 0⟩ [fm]⊢* ⟨0, b, c, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by omega,
      show c + (k + 1) = (c + k) + 1 from by omega]
  step fm
  apply stepStar_trans (ih b c (d+1))
  rw [show d + 1 + k = d + (k + 1) from by omega]
  finish

-- R4 chain: k rounds consuming b and d, building e
theorem r4_chain : ∀ k, ∀ b d e,
    ⟨0, b+k, 0, d+k, e⟩ [fm]⊢* ⟨0, b, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by omega,
      show d + (k + 1) = (d + k) + 1 from by omega]
  step fm
  apply stepStar_trans (ih b d (e+1))
  rw [show e + 1 + k = e + (k + 1) from by omega]
  finish

-- Main transition: (0, 0, 0, d+1, e+1) →⁺ (0, 0, 0, d+2, 3*e+2)
theorem main_trans : ⟨0, 0, 0, d+1, e+1⟩ [fm]⊢⁺ ⟨(0:ℕ), 0, 0, d+2, 3*e+2⟩ := by
  -- Phase 1 (R5): → (0,0,1,d,e+1)
  step fm
  -- Phase 2 (R2,R1,R1 × (e+1)): → (0, 4*e+4, e+2, d+2*e+2, 0)
  apply stepStar_trans (r2r1r1_chain e 0 0 d)
  simp only [Nat.zero_add]
  -- Phase 3 (R3 × (e+2)): → (0, 3*e+2, 0, d+3*e+4, 0)
  have h3 := r3_chain (e+2) (3*e+2) 0 (d+2*e+2)
  rw [show 3*e+2+(e+2) = 4*e+4 from by omega,
      show 0+(e+2) = e+2 from by omega,
      show d+2*e+2+(e+2) = d+3*e+4 from by omega] at h3
  apply stepStar_trans h3
  -- Phase 4 (R4 × (3*e+2)): → (0, 0, 0, d+2, 3*e+2)
  have h4 := r4_chain (3*e+2) 0 (d+2) 0
  rw [show 0+(3*e+2) = 3*e+2 from by omega,
      show d+2+(3*e+2) = d+3*e+4 from by omega] at h4
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d+1, e+1⟩) ⟨0, 0⟩
  intro ⟨d, e⟩; exact ⟨⟨d+1, 3*e+1⟩, main_trans⟩
