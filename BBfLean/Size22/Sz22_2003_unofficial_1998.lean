import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1998: [99/35, 5/6, 8/5, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  1  0  0
 3  0 -1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1998

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 chain: move e to d.
theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- R1R2 interleave: alternating R1 and R2, draining d.
theorem r1r2_interleave : ∀ k, ⟨A + k, B, 1, k, E⟩ [fm]⊢* ⟨A, B + k, 1, 0, E + k⟩ := by
  intro k; induction' k with k ih generalizing A B E
  · exists 0
  · rw [show A + (k + 1) = (A + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (A := A) (B := B + 1) (E := E + 1))
    ring_nf; finish

-- R2 chain: drain a and b simultaneously (d=0).
theorem r2_drain : ∀ k, ∀ C, ⟨A + k, k, C, 0, E⟩ [fm]⊢* ⟨A, 0, C + k, 0, E⟩ := by
  intro k; induction' k with k ih generalizing A
  · intro C; exists 0
  · intro C
    rw [show A + (k + 1) = (A + k) + 1 from by ring]
    apply stepStar_trans (c₂ := ⟨A + k, k, C + 1, 0, E⟩)
    · apply step_stepStar
      show fm ⟨(A + k) + 1, k + 1, C, 0, E⟩ = some ⟨A + k, k, C + 1, 0, E⟩
      simp [fm]
    · have h := ih (C + 1) (A := A)
      rw [show C + 1 + k = C + (k + 1) from by ring] at h
      exact h

-- R3 chain: convert c to a (b=0, d=0).
theorem r3_chain : ∀ k, ⟨A, 0, k, 0, E⟩ [fm]⊢* ⟨A + 3 * k, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih generalizing A
  · exists 0
  · step fm
    apply stepStar_trans (ih (A := A + 3))
    ring_nf; finish

-- Main transition:
-- (F + 2*e + 3, 0, 0, 0, e+1) →⁺ (F + 3*e + 6, 0, 0, 0, e+2)
theorem main_trans : ⟨F + 2 * e + 3, 0, 0, 0, e + 1⟩ [fm]⊢⁺
    ⟨F + 3 * e + 6, 0, 0, 0, e + 2⟩ := by
  -- Phase 1: e_to_d.
  rw [show e + 1 = 0 + (e + 1) from by omega]
  apply stepStar_stepPlus_stepPlus (e_to_d (e + 1) (a := F + 2 * e + 3) (d := 0) (e := 0))
  rw [show 0 + (e + 1) = e + 1 from by omega]
  -- Phase 2: R5 step.
  rw [show F + 2 * e + 3 = (F + 2 * e + 2) + 1 from by omega]
  step fm
  -- Phase 3: r1r2_interleave with k = e+1.
  rw [show F + 2 * e + 2 = (F + e + 1) + (e + 1) from by ring]
  apply stepStar_trans (r1r2_interleave (e + 1) (A := F + e + 1) (B := 0) (E := 1))
  -- Phase 4: r2_drain with k = e+1.
  rw [show (0 : ℕ) + (e + 1) = e + 1 from by omega,
      show F + e + 1 = F + (e + 1) from by ring,
      show (1 : ℕ) + (e + 1) = e + 2 from by omega]
  apply stepStar_trans (r2_drain (e + 1) 1 (A := F) (E := e + 2))
  -- Phase 5: r3_chain with k = e+2.
  rw [show (1 : ℕ) + (e + 1) = e + 2 from by omega]
  apply stepStar_trans (r3_chain (e + 2) (A := F) (E := e + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨F, e⟩ ↦ ⟨F + 2 * e + 3, 0, 0, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨F, e⟩
  refine ⟨⟨F + e + 1, e + 1⟩, ?_⟩
  show ⟨F + 2 * e + 3, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨(F + e + 1) + 2 * (e + 1) + 3, 0, 0, 0, (e + 1) + 1⟩
  rw [show (F + e + 1) + 2 * (e + 1) + 3 = F + 3 * e + 6 from by ring,
      show (e + 1) + 1 = e + 2 from by ring]
  exact main_trans

end Sz22_2003_unofficial_1998
