import BBfLean.FM

/-!
# sz22_2003_unofficial #304: [15/2, 44/21, 1/3, 49/5, 1/77, 3/7]

Vector representation:
```
-1  1  1  0  0
 2 -1  0 -1  1
 0 -1  0  0  0
 0  0 -1  2  0
 0  0  0 -1 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_304

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 repeated: drain b
theorem r3_drain (b n c e : ℕ) :
    ⟨0, b + n, c, 0, e⟩ [fm]⊢* (⟨0, b, c, 0, e⟩ : Q) := by
  induction n with
  | zero => exists 0
  | succ n ih =>
    rw [show b + (n + 1) = (b + n) + 1 from by omega]
    step fm; exact ih

-- R4 repeated: convert c to d
theorem r4_drain (n d e : ℕ) :
    ⟨0, 0, n, d, e⟩ [fm]⊢* (⟨0, 0, 0, d + 2 * n, e⟩ : Q) := by
  induction n generalizing d with
  | zero => simp; exists 0
  | succ n ih =>
    step fm
    rw [show d + 2 * (n + 1) = (d + 2) + 2 * n from by omega]
    exact ih (d + 2)

-- R5 repeated: drain e
theorem r5_drain (n d : ℕ) :
    ⟨0, 0, 0, d + n, n⟩ [fm]⊢* (⟨0, 0, 0, d, 0⟩ : Q) := by
  induction n generalizing d with
  | zero => exists 0
  | succ n ih =>
    rw [show d + (n + 1) = (d + n) + 1 from by omega]
    step fm; exact ih d

-- R2+R1+R1 loop: the main computation phase
theorem r2r1r1_loop (k n : ℕ) :
    ⟨0, k + 1, 2 * k, n + 1, k⟩ [fm]⊢* (⟨0, k + n + 2, 2 * (k + n + 1), 0, k + n + 1⟩ : Q) := by
  induction n generalizing k with
  | zero =>
    step fm; step fm; step fm
    show ⟨0, k + 1 + 1, 2 * k + 1 + 1, 0, k + 1⟩ [fm]⊢*
      (⟨0, k + 0 + 2, 2 * (k + 0 + 1), 0, k + 0 + 1⟩ : Q)
    simp only [Nat.add_zero]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by omega,
        show k + 1 + 1 = k + 2 from by omega]
    finish
  | succ n ih =>
    step fm; step fm; step fm
    show ⟨0, k + 1 + 1, 2 * k + 1 + 1, n + 1, k + 1⟩ [fm]⊢*
      (⟨0, k + (n + 1) + 2, 2 * (k + (n + 1) + 1), 0, k + (n + 1) + 1⟩ : Q)
    rw [show k + 1 + 1 = (k + 1) + 1 from by omega,
        show 2 * k + 1 + 1 = 2 * (k + 1) from by omega,
        show k + (n + 1) + 2 = (k + 1) + n + 2 from by omega,
        show 2 * (k + (n + 1) + 1) = 2 * ((k + 1) + n + 1) from by omega,
        show k + (n + 1) + 1 = (k + 1) + n + 1 from by omega]
    exact ih (k + 1)

-- Main transition: (0,0,0,d+2,0) →⁺ (0,0,0,3*d+3,0)
theorem main_trans (d : ℕ) : ⟨0, 0, 0, d + 2, 0⟩ [fm]⊢⁺ (⟨0, 0, 0, 3 * d + 3, 0⟩ : Q) := by
  -- Phase 1: R6 step
  step fm
  -- Phase 2: R2+R1+R1 loop
  have h2 := r2r1r1_loop 0 d
  simp only [Nat.zero_add, Nat.mul_zero] at h2
  apply stepStar_trans h2
  -- Phase 3: R3 drain b
  have h3 := r3_drain 0 (d + 2) (2 * (d + 1)) (d + 1)
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  -- Phase 4: R4 drain c
  have h4 := r4_drain (2 * (d + 1)) 0 (d + 1)
  simp only [Nat.zero_add] at h4
  apply stepStar_trans h4
  -- Phase 5: R5 drain e
  rw [show 2 * (2 * (d + 1)) = (3 * d + 3) + (d + 1) from by omega]
  exact r5_drain (d + 1) (3 * d + 3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨0, 0, 0, 2, 0⟩ : Q))
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d, q = (⟨0, 0, 0, d + 2, 0⟩ : Q))
  · intro c ⟨d, hq⟩; subst hq
    refine ⟨⟨0, 0, 0, 3 * d + 3, 0⟩, ⟨3 * d + 1, ?_⟩, main_trans d⟩
    simp
  · exact ⟨0, rfl⟩
