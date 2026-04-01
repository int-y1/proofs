import BBfLean.FM

/-!
# sz22_2003_unofficial #1522: [7/30, 11/2, 12/77, 25/11, 14/5]

Vector representation:
```
-1 -1 -1  1  0
-1  0  0  0  1
 2  1  0 -1 -1
 0  0  2  0 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1522

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3,R2,R2 spiral: each round b += 1, d -= 1, e += 1
theorem spiral_phase : ∀ d b, ⟨0, b, 0, d + 1, b + 1⟩ [fm]⊢* ⟨0, b + d + 1, 0, 0, b + d + 2⟩ := by
  intro d; induction' d with d ih <;> intro b
  · step fm; step fm; step fm; finish
  · step fm; step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by omega]
    apply stepStar_trans (ih (b + 1))
    show ⟨0, b + 1 + d + 1, 0, 0, b + 1 + d + 2⟩ [fm]⊢* ⟨0, b + (d + 1) + 1, 0, 0, b + (d + 1) + 2⟩
    have h1 : b + 1 + d + 1 = b + (d + 1) + 1 := by omega
    have h2 : b + 1 + d + 2 = b + (d + 1) + 2 := by omega
    rw [h1, h2]; finish

-- R4 chain: convert e to c
theorem r4_chain : ∀ e, ⟨0, b, c, 0, e⟩ [fm]⊢* ⟨0, b, c + 2 * e, 0, 0⟩ := by
  intro e; induction' e with e ih generalizing c
  · exists 0
  · step fm
    apply stepStar_trans (ih (c := c + 2))
    show ⟨0, b, c + 2 + 2 * e, 0, 0⟩ [fm]⊢* ⟨0, b, c + 2 * (e + 1), 0, 0⟩
    have : c + 2 + 2 * e = c + 2 * (e + 1) := by omega
    rw [this]; finish

-- R5,R1 chain: drain b while converting c to d
theorem r5r1_drain : ∀ b, ⟨0, b + 1, 2 * b + 4, d, 0⟩ [fm]⊢* ⟨0, 0, 2, d + 2 * b + 2, 0⟩ := by
  intro b; induction' b with b ih generalizing d
  · step fm; step fm; finish
  · rw [show 2 * (b + 1) + 4 = (2 * b + 4) + 2 from by omega,
        show b + 1 + 1 = (b + 1) + 1 from by omega]
    step fm; step fm
    apply stepStar_trans (ih (d := d + 2))
    show ⟨0, 0, 2, d + 2 + 2 * b + 2, 0⟩ [fm]⊢* ⟨0, 0, 2, d + 2 * (b + 1) + 2, 0⟩
    have : d + 2 + 2 * b + 2 = d + 2 * (b + 1) + 2 := by omega
    rw [this]; finish

-- Final 4 steps: (0, 0, 2, D, 0) →⁺ (1, 0, 0, D+1, 0)
theorem final_steps : ⟨0, 0, 2, D, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, D + 1, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Main transition
theorem main_trans : ⟨1, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 2 * d + 3, 0⟩ := by
  step fm
  show ⟨0, 0, 0, d + 1, 0 + 1⟩ [fm]⊢* ⟨1, 0, 0, 2 * d + 3, 0⟩
  apply stepStar_trans (spiral_phase d 0)
  show ⟨0, 0 + d + 1, 0, 0, 0 + d + 2⟩ [fm]⊢* ⟨1, 0, 0, 2 * d + 3, 0⟩
  rw [show 0 + d + 1 = d + 1 from by omega, show 0 + d + 2 = d + 2 from by omega]
  apply stepStar_trans (r4_chain (d + 2) (b := d + 1) (c := 0))
  rw [show 0 + 2 * (d + 2) = 2 * d + 4 from by omega]
  apply stepStar_trans (r5r1_drain d (d := 0))
  rw [show 0 + 2 * d + 2 = 2 * d + 2 from by omega]
  exact stepPlus_stepStar (final_steps (D := 2 * d + 2))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨1, 0, 0, d + 1, 0⟩) 0
  intro d; exists 2 * d + 2
  exact main_trans
