import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #625: [35/6, 143/2, 4/55, 3/7, 105/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  1  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_625

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d+1, e, f⟩
  | _ => none

-- R4 repeated: drain d to b
theorem d_to_b : ∀ k b, ⟨(0:ℕ), b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h (b + 1))
  ring_nf; finish

-- [R1, R1, R3] chain
theorem r1r1r3_chain : ∀ k j, ⟨(2:ℕ), 2*k+1, j, 2*j+1, k, F⟩ [fm]⊢*
    ⟨1, 0, j+k+1, 2*j+2*k+2, 0, F⟩ := by
  intro k; induction' k with k h <;> intro j
  · step fm; ring_nf; finish
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega]
  step fm; step fm; step fm
  apply stepStar_trans (h (j + 1))
  ring_nf; finish

-- R5, R3, then r1r1r3_chain
theorem phase2 (n : ℕ) : ⟨(0:ℕ), 2*n, 0, 0, n+1, F+1⟩ [fm]⊢*
    ⟨1, 0, n+1, 2*n+2, 0, F⟩ := by
  step fm; step fm
  have h := @r1r1r3_chain F n 0
  simp only [Nat.zero_add] at h
  rw [show 2 * 0 + 2 * n + 2 = 2 * n + 2 from by ring] at h
  exact h

-- R2, R3: first step of Phase 3
theorem phase3a (c d f : ℕ) : ⟨(1:ℕ), 0, c+1, d, 0, f⟩ [fm]⊢* ⟨2, 0, c, d, 0, f+1⟩ := by
  step fm; step fm; ring_nf; finish

-- [R2, R2, R3] chain
theorem r2r2r3_chain : ∀ k c e f, ⟨(2:ℕ), 0, c + k, d, e, f⟩ [fm]⊢*
    ⟨2, 0, c, d, e + k, f + 2 * k⟩ := by
  intro k; induction' k with k h <;> intro c e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega]
  step fm; step fm; step fm
  apply stepStar_trans (h c (e + 1) (f + 1 + 1))
  ring_nf; finish

-- Final R2, R2
theorem phase3c (d e f : ℕ) : ⟨(2:ℕ), 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e+2, f+2⟩ := by
  step fm; step fm; ring_nf; finish

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨(0:ℕ), 0, 0, 2*(n+1), n+2, (n+1)*(n+1)+(n+1)+1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*(n+2), n+3, (n+2)*(n+2)+(n+2)+1⟩ := by
  -- Take one R4 step for ⊢⁺
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by omega]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  -- Now at (0, 1, 0, 2*n+1, n+2, ...)
  -- Continue draining d to b
  have p1 : ⟨(0:ℕ), 1, 0, 2*n+1, n+2, (n+1)*(n+1)+(n+1)+1⟩ [fm]⊢*
      ⟨0, 2*(n+1), 0, 0, n+2, (n+1)*(n+1)+(n+1)+1⟩ := by
    have h := d_to_b (d := 0) (e := n+2) (f := (n+1)*(n+1)+(n+1)+1) (2*n+1) 1
    simp only [Nat.zero_add] at h
    rw [show (1:ℕ) + (2 * n + 1) = 2 * (n + 1) from by ring] at h
    exact h
  -- Phase 2
  have p2 : ⟨(0:ℕ), 2*(n+1), 0, 0, n+2, (n+1)*(n+1)+(n+1)+1⟩ [fm]⊢*
      ⟨1, 0, n+2, 2*n+2+2, 0, (n+1)*(n+1)+(n+1)⟩ := by
    rw [show n + 2 = (n+1) + 1 from by omega,
        show (n+1)*(n+1)+(n+1)+1 = ((n+1)*(n+1)+(n+1)) + 1 from by omega]
    have h := phase2 (F := (n+1)*(n+1)+(n+1)) (n+1)
    rw [show 2 * (n + 1) + 2 = 2 * n + 2 + 2 from by ring] at h
    exact h
  -- Phase 3a
  have p3a : ⟨(1:ℕ), 0, n+2, 2*n+2+2, 0, (n+1)*(n+1)+(n+1)⟩ [fm]⊢*
      ⟨2, 0, n+1, 2*n+2+2, 0, (n+1)*(n+1)+(n+1)+1⟩ := by
    rw [show n + 2 = (n+1) + 1 from by omega]
    exact phase3a (n+1) (2*n+2+2) ((n+1)*(n+1)+(n+1))
  -- Phase 3b
  have p3b : ⟨(2:ℕ), 0, n+1, 2*n+2+2, 0, (n+1)*(n+1)+(n+1)+1⟩ [fm]⊢*
      ⟨2, 0, 0, 2*n+2+2, n+1, (n+1)*(n+1)+3*(n+1)+1⟩ := by
    have h := @r2r2r3_chain (2*n+2+2) (n+1) 0 0 ((n+1)*(n+1)+(n+1)+1)
    simp only [Nat.zero_add] at h
    rw [show (n+1)*(n+1)+(n+1)+1+2*(n+1) = (n+1)*(n+1)+3*(n+1)+1 from by ring] at h
    exact h
  -- Phase 3c
  have p3c : ⟨(2:ℕ), 0, 0, 2*n+2+2, n+1, (n+1)*(n+1)+3*(n+1)+1⟩ [fm]⊢*
      ⟨0, 0, 0, 2*n+2+2, n+3, (n+1)*(n+1)+3*(n+1)+3⟩ := by
    exact phase3c (2*n+2+2) (n+1) ((n+1)*(n+1)+3*(n+1)+1)
  -- Compose
  have goal : ⟨(0:ℕ), 1, 0, 2*n+1, n+2, (n+1)*(n+1)+(n+1)+1⟩ [fm]⊢*
      ⟨0, 0, 0, 2*n+2+2, n+3, (n+1)*(n+1)+3*(n+1)+3⟩ :=
    stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3a (stepStar_trans p3b p3c)))
  rw [show 2*(n+2) = 2*n+2+2 from by ring,
      show (n+2)*(n+2)+(n+2)+1 = (n+1)*(n+1)+3*(n+1)+3 from by ring]
  exact goal

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2*(n+1), n+2, (n+1)*(n+1)+(n+1)+1⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_625
